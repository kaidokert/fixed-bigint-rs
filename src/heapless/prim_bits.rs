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
                // LSB-to-MSB; stop at the first non-zero limb.
                let mut ret = 0u32;
                let mut i = 0;
                while i < n {
                    let v = self.limbs[i];
                    ret += <T as PrimBits>::trailing_zeros(v);
                    if !is_zero(&v) {
                        break;
                    }
                    i += 1;
                }
                ret
            }
            // Shared full-width branchless scan (see `const_trailing_zeros_ct`).
            PersonalityTag::Ct => crate::fixeduint::const_trailing_zeros_ct(&self.limbs[..n]),
        }
    }

    fn swap_bytes(self) -> Self {
        // Reverse limb order over the value width, each limb byte-swapped.
        let n = self.len as usize;
        let mut limbs = [zero::<T>(); CAP];
        let mut i = 0;
        while i < n {
            limbs[i] = self.limbs[n - 1 - i].swap_bytes();
            i += 1;
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
        let mut i = 0;
        while i < n {
            limbs[n - 1 - i] = self.limbs[i].reverse_bits();
            i += 1;
        }
        Self {
            limbs,
            len: self.len,
            _p: PhantomData,
        }
    }

    fn rotate_left(self, n: u32) -> Self {
        let bit_size = self.len as u32 * (core::mem::size_of::<T>() as u32 * 8);
        if bit_size == 0 {
            return self;
        }
        let shift = (n % bit_size) as usize;
        let a = self << shift;
        let b = self >> (bit_size as usize - shift);
        a | b
    }

    fn rotate_right(self, n: u32) -> Self {
        let bit_size = self.len as u32 * (core::mem::size_of::<T>() as u32 * 8);
        if bit_size == 0 {
            return self;
        }
        let shift = (n % bit_size) as usize;
        let a = self >> shift;
        let b = self << (bit_size as usize - shift);
        a | b
    }

    fn unsigned_shl(self, n: u32) -> Self {
        self << (n as usize)
    }

    fn unsigned_shr(self, n: u32) -> Self {
        self >> (n as usize)
    }

    fn signed_shl(self, n: u32) -> Self {
        // Unsigned carrier: identical to unsigned_shl.
        self << (n as usize)
    }

    fn signed_shr(self, n: u32) -> Self {
        // Unsigned carrier: the sign bit is always 0, so logical == arithmetic.
        self >> (n as usize)
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

    #[test]
    fn parity_full_width() {
        // 32 bytes, top byte non-zero → both carriers at 8 limbs.
        let b = [
            0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF, 0x10, 0x32, 0x54, 0x76, 0x98, 0xBA,
            0xDC, 0xFE, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB,
            0xCC, 0xDD, 0xEE, 0xFF,
        ];
        assert_parity(
            HeaplessBigInt::<u32, 8, Nct>::from_le_bytes(&b),
            FixedUInt::<u32, 8, Nct>::from_le_bytes(&b),
        );
    }

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
