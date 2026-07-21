//! `const_num_traits::PrimBits` for `HeaplessBigInt` — the bit-operation
//! vocabulary (count / scan / rotate / reverse / byte-swap / shift),
//! personality-generic.
//!
//! Every width-sensitive member operates over the value width
//! (`len·word_bits`), never `CAP`: a value at `len = k` returns exactly
//! what the same-width `FixedUInt<T, k>` returns. `count_ones`/`count_zeros`
//! are uniform across personalities (any CT weakness in `T::count_ones` is
//! inherited by both, same as `FixedUInt`); `leading_zeros`/`trailing_zeros`
//! branch on `P::TAG` and share `FixedUInt`'s `black_box`-guarded Ct scans.
//! `leading_ones`/`trailing_ones` use the trait defaults (`(!self).*_zeros()`),
//! which are correct given the value-width `Not`.
//!
//! `pow` and the `num_traits::PrimInt` bridge are deliberately absent:
//! `PrimInt` supertrait-requires `CheckedDiv`/`Saturating`/`Num`, which
//! `HeaplessBigInt` does not implement yet.

use super::{HeaplessBigInt, is_zero, zero};
use crate::MachineWord;
use const_num_traits::{Personality, PersonalityTag, PrimBits};
use core::marker::PhantomData;

/// Value width in bits (`len·word_bits`) — the width every PrimBits member
/// operates over. `len <= u16::MAX` and `word_bits <= 64`, so it fits `u32`.
#[inline]
fn value_bits<T: MachineWord, const CAP: usize, P: Personality>(
    v: &HeaplessBigInt<T, CAP, P>,
) -> u32 {
    v.len as u32 * (core::mem::size_of::<T>() as u32 * 8)
}

/// Fixed-width zero at a given `len` (all `CAP` limbs zero).
#[inline]
fn zero_at<T: MachineWord, const CAP: usize, P: Personality>(
    len: u16,
) -> HeaplessBigInt<T, CAP, P> {
    HeaplessBigInt {
        limbs: [zero::<T>(); CAP],
        len,
        _p: PhantomData,
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> PrimBits for HeaplessBigInt<T, CAP, P> {
    fn count_ones(self) -> u32 {
        let n = self.len as usize;
        let mut count = 0u32;
        for &w in &self.limbs[..n] {
            count += w.count_ones();
        }
        count
    }

    fn count_zeros(self) -> u32 {
        let n = self.len as usize;
        let mut count = 0u32;
        for &w in &self.limbs[..n] {
            count += w.count_zeros();
        }
        count
    }

    fn leading_zeros(self) -> u32 {
        // Delegate to the inherent `leading_zeros` (bits.rs), which handles
        // both personalities at value width. The `&self` borrow is required,
        // not needless — it selects the inherent `&self` method; without it,
        // method resolution picks this by-value trait method and recurses.
        #[allow(clippy::needless_borrow)]
        let lz = (&self).leading_zeros();
        lz as u32
    }

    fn trailing_zeros(self) -> u32 {
        let n = self.len as usize;
        match P::TAG {
            PersonalityTag::Nct => {
                // LSB-to-MSB; stop at the first non-zero limb. Iterating the
                // slice keeps the loop bounds-check-free.
                let mut ret = 0u32;
                for &v in &self.limbs[..n] {
                    ret += <T as PrimBits>::trailing_zeros(v);
                    if !is_zero(&v) {
                        break;
                    }
                }
                ret
            }
            // Shared full-width branchless scan (see `const_trailing_zeros_ct`).
            PersonalityTag::Ct => {
                let s = self.limbs.get(..n).unwrap_or(&self.limbs);
                crate::fixeduint::const_trailing_zeros_ct(s)
            }
        }
    }

    fn swap_bytes(self) -> Self {
        // Reverse limb order over the value width, each limb byte-swapped.
        let n = self.len as usize;
        let mut limbs = [zero::<T>(); CAP];
        for (o, i) in limbs[..n].iter_mut().zip(self.limbs[..n].iter().rev()) {
            *o = i.swap_bytes();
        }
        Self {
            limbs,
            len: self.len,
            _p: PhantomData,
        }
    }

    fn reverse_bits(self) -> Self {
        // Reverse limb order and every limb's bits, over the value width.
        let n = self.len as usize;
        let mut limbs = [zero::<T>(); CAP];
        for (o, i) in limbs[..n].iter_mut().rev().zip(self.limbs[..n].iter()) {
            *o = i.reverse_bits();
        }
        Self {
            limbs,
            len: self.len,
            _p: PhantomData,
        }
    }

    fn rotate_left(self, n: u32) -> Self {
        let bits = value_bits(&self);
        if bits == 0 {
            return self;
        }
        let shift = n % bits;
        if shift == 0 {
            return self;
        }
        // `shift` and `bits - shift` are both in `1..bits` (< u16::MAX·64),
        // so the usize casts are lossless even where `usize` is 16-bit.
        let a = self << shift as usize;
        let b = self >> (bits - shift) as usize;
        a | b
    }

    fn rotate_right(self, n: u32) -> Self {
        let bits = value_bits(&self);
        if bits == 0 {
            return self;
        }
        let shift = n % bits;
        if shift == 0 {
            return self;
        }
        let a = self >> shift as usize;
        let b = self << (bits - shift) as usize;
        a | b
    }

    fn unsigned_shl(self, n: u32) -> Self {
        // Shifting by >= the value width clears it. The guard also keeps the
        // `as usize` cast below lossless on a 16-bit-`usize` target.
        if n >= value_bits(&self) {
            return zero_at(self.len);
        }
        self << n as usize
    }

    fn unsigned_shr(self, n: u32) -> Self {
        if n >= value_bits(&self) {
            return zero_at(self.len);
        }
        // `>>` narrows `len` on whole-word shifts, but PrimBits is fixed-width:
        // restore the operand width so downstream width-sensitive ops
        // (count_zeros, leading_zeros) match FixedUInt. The freed high limbs
        // are already zero, so bumping `len` back is value-preserving.
        let mut r = self >> n as usize;
        r.len = self.len;
        r
    }

    fn signed_shl(self, n: u32) -> Self {
        // Unsigned carrier: identical to unsigned_shl (mirrors FixedUInt).
        <Self as PrimBits>::unsigned_shl(self, n)
    }

    fn signed_shr(self, n: u32) -> Self {
        // Unsigned carrier: heapless mirrors FixedUInt, which shifts logically
        // (treats the value as unsigned), keeping the two carriers bit-for-bit.
        <Self as PrimBits>::unsigned_shr(self, n)
    }

    // Little-endian host: in-memory order already matches, so to/from_le are
    // no-ops and to/from_be byte-swap. Big-endian hosts unsupported, same as
    // FixedUInt.
    fn from_be(x: Self) -> Self {
        x.swap_bytes()
    }

    fn from_le(x: Self) -> Self {
        x
    }

    fn to_be(self) -> Self {
        self.swap_bytes()
    }

    fn to_le(self) -> Self {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FixedUInt;
    use const_num_traits::{Ct, Nct};

    // Differential: at width N, HeaplessBigInt<u32, CAP> carried at len = N
    // must return exactly what FixedUInt<u32, N> returns for every PrimBits
    // member. FixedUInt is the trusted reference.
    fn assert_parity<const CAP: usize, const N: usize>(
        h: HeaplessBigInt<u32, CAP, Nct>,
        f: FixedUInt<u32, N, Nct>,
    ) {
        assert_eq!(h.len as usize, N, "test pattern must fill exactly N limbs");
        assert_eq!(
            PrimBits::count_ones(h),
            PrimBits::count_ones(f),
            "count_ones"
        );
        assert_eq!(
            PrimBits::count_zeros(h),
            PrimBits::count_zeros(f),
            "count_zeros"
        );
        assert_eq!(PrimBits::leading_zeros(h), PrimBits::leading_zeros(f), "lz");
        assert_eq!(
            PrimBits::trailing_zeros(h),
            PrimBits::trailing_zeros(f),
            "tz"
        );
        assert_eq!(PrimBits::leading_ones(h), PrimBits::leading_ones(f), "lo");
        assert_eq!(PrimBits::trailing_ones(h), PrimBits::trailing_ones(f), "to");
        assert_eq!(
            &PrimBits::swap_bytes(h).limbs[..N],
            &PrimBits::swap_bytes(f).array[..]
        );
        assert_eq!(
            &PrimBits::reverse_bits(h).limbs[..N],
            &PrimBits::reverse_bits(f).array[..]
        );
        assert_eq!(
            &PrimBits::to_be(h).limbs[..N],
            &PrimBits::to_be(f).array[..]
        );
        assert_eq!(
            &PrimBits::from_be(h).limbs[..N],
            &PrimBits::from_be(f).array[..]
        );
        assert_eq!(&(!h).limbs[..N], &(!f).array[..], "not");
        for k in [0u32, 1, 5, 31, 33, 100, 255] {
            assert_eq!(
                &PrimBits::rotate_left(h, k).limbs[..N],
                &PrimBits::rotate_left(f, k).array[..],
                "rotl {k}"
            );
            assert_eq!(
                &PrimBits::rotate_right(h, k).limbs[..N],
                &PrimBits::rotate_right(f, k).array[..],
                "rotr {k}"
            );
            assert_eq!(
                &PrimBits::unsigned_shl(h, k).limbs[..N],
                &PrimBits::unsigned_shl(f, k).array[..],
                "ushl {k}"
            );
            assert_eq!(
                &PrimBits::unsigned_shr(h, k).limbs[..N],
                &PrimBits::unsigned_shr(f, k).array[..],
                "ushr {k}"
            );
            assert_eq!(
                &PrimBits::signed_shr(h, k).limbs[..N],
                &PrimBits::signed_shr(f, k).array[..],
                "sshr {k}"
            );
        }
    }

    // Full-width parity across both carriers lives in the generic
    // `tests/carrier_generic.rs` harness (`prim_bits_bit_vocabulary`). What
    // stays here is heapless-only: the sub-capacity value-width guarantee and
    // the Ct-scan behavior, neither of which the fixed-width harness can reach.
    #[test]
    fn parity_sub_capacity_is_value_width() {
        // 8 bytes → len 2 inside a CAP-8 carrier. Must mirror FixedUInt<u32,2>,
        // NOT the CAP-8 width: this is the value-width guarantee.
        let b = [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0x80];
        assert_parity(
            HeaplessBigInt::<u32, 8, Nct>::from_le_bytes(&b),
            FixedUInt::<u32, 2, Nct>::from_le_bytes(&b),
        );
    }

    #[test]
    fn shr_preserves_value_width() {
        // PrimBits shifts are fixed-width, unlike the `>>` operator which
        // narrows `len` on whole-word shifts. Without width preservation,
        // count_zeros/leading_zeros after the shift report the wrong width.
        let h = HeaplessBigInt::<u32, 8, Nct>::from_le_bytes(&[0, 0, 0, 0, 0, 0, 0, 0x80]); // len 2
        let f = FixedUInt::<u32, 2, Nct>::from_le_bytes(&[0, 0, 0, 0, 0, 0, 0, 0x80]);
        let hs = PrimBits::unsigned_shr(h, 32);
        assert_eq!(hs.len, 2, "shr must preserve the operand width");
        assert_eq!(
            PrimBits::count_zeros(hs),
            PrimBits::count_zeros(f >> 32usize)
        );
        assert_eq!(
            PrimBits::leading_zeros(hs),
            PrimBits::leading_zeros(f >> 32usize)
        );
        // Over-shift clears to a fixed-width zero, not a narrowed one.
        let hz = PrimBits::unsigned_shr(h, 999);
        assert_eq!(hz.len, 2);
        assert_eq!(PrimBits::count_zeros(hz), 64);
    }

    #[test]
    fn ct_scans_match_nct() {
        // The Ct personality's full-width scans return the same magnitude as
        // Nct for the same value (they differ only in timing).
        let b = [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80];
        let hn = HeaplessBigInt::<u32, 8, Nct>::from_le_bytes(&b);
        let hc = HeaplessBigInt::<u32, 8, Ct>::from_le_bytes(&b);
        assert_eq!(PrimBits::trailing_zeros(hc), PrimBits::trailing_zeros(hn));
        assert_eq!(PrimBits::leading_zeros(hc), PrimBits::leading_zeros(hn));
        assert_eq!(PrimBits::count_ones(hc), PrimBits::count_ones(hn));
    }

    #[test]
    fn not_is_value_width() {
        // !x over one limb: 0x0000_00FF → 0xFFFF_FF00, len stays 1.
        let x = HeaplessBigInt::<u32, 8, Nct>::from_le_bytes(&[0xFF]);
        let n = !x;
        assert_eq!(n.len, 1);
        assert_eq!(n.limbs[0], 0xFFFF_FF00);
    }
}
