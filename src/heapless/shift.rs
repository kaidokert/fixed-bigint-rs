//! `Shl<usize>` / `Shr<usize>` for `HeaplessBigInt`.
//!
//! Bit-count shifts by a public `usize` amount. Output `len` is derived
//! from operand `len` + shift amount, both public shape parameters. The
//! shape math:
//!
//! - `Shl`: width-preserving — `out_len = self.len`, bits shifted past the
//!   operand width are discarded (`x << bits mod 2^(len·word_bits)`), so a
//!   value at `len = k` shifts exactly like `FixedUInt<T, k>`. `CAP` never
//!   enters; the words beyond `len` do not exist. A caller wanting the
//!   shifted value to occupy more words constructs it at the wider width
//!   first (as `div_rem` does).
//! - `Shr`: `out_len = self.len.saturating_sub(bits / word_bits)` on `Nct`. The
//!   top limb may become zero — that's fine under the zero-tail invariant
//!   and downstream can trim explicitly if needed.
//!
//! Personality dispatch: the `Nct` arms take the direct word/bit shift above
//! (branching on the amount, fine for a public amount). The `Ct` arms route
//! through the branchless barrels [`const_shl_ct`] / [`const_shr_ct`] so a
//! secret shift amount never drives control flow — and `Ct` `Shr` is
//! width-preserving, since a data-dependent `len` shrink would itself leak.

use super::{HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::{Bounded, Personality, PersonalityTag};
use core::marker::PhantomData;
use core::ops::{Shl, ShlAssign, Shr, ShrAssign};

/// Width-preserving left shift by a **public** `bits`: the raw word/bit-shift
/// body, output `len == value.len`. Branches on `word_shift`/`bit_shift`, so it
/// is only ever called with a public amount (the `Nct` operator arm, or a
/// barrel stage `2^k`). The `Ct` operator arm routes through [`const_shl_ct`]
/// instead so a secret amount never reaches this branchful body.
fn shl_wp<T: MachineWord, const CAP: usize, P: Personality>(
    value: HeaplessBigInt<T, CAP, P>,
    bits: usize,
) -> HeaplessBigInt<T, CAP, P> {
    let word_bits = core::mem::size_of::<T>() * 8;
    let word_shift = bits / word_bits;
    let bit_shift = bits % word_bits;
    let out_len = value.len as usize;
    let mut limbs = [zero::<T>(); CAP];
    let mut i = 0;
    while i < out_len {
        let dst_lo = i + word_shift;
        if dst_lo < out_len {
            limbs[dst_lo] |= value.limbs[i] << bit_shift;
            if bit_shift > 0 {
                let dst_hi = dst_lo + 1;
                if dst_hi < out_len {
                    limbs[dst_hi] |= value.limbs[i] >> (word_bits - bit_shift);
                }
            }
        }
        i += 1;
    }
    HeaplessBigInt {
        limbs,
        len: value.len,
        _p: PhantomData,
    }
}

/// Width-preserving right shift by a **public** `bits`, output `len ==
/// value.len` (the top limbs zero-fill rather than the `len` shrinking as the
/// `Nct` `Shr` operator does). Public-only, like [`shl_wp`]; a secret amount
/// goes through [`const_shr_ct`].
fn shr_wp<T: MachineWord, const CAP: usize, P: Personality>(
    value: HeaplessBigInt<T, CAP, P>,
    bits: usize,
) -> HeaplessBigInt<T, CAP, P> {
    let word_bits = core::mem::size_of::<T>() * 8;
    let word_shift = bits / word_bits;
    let bit_shift = bits % word_bits;
    let n = value.len as usize;
    let mut limbs = [zero::<T>(); CAP];
    let mut i = 0;
    while i < n {
        let src_lo = i + word_shift;
        let lo = if src_lo < n {
            value.limbs[src_lo] >> bit_shift
        } else {
            zero::<T>()
        };
        let hi = if bit_shift > 0 && src_lo + 1 < n {
            value.limbs[src_lo + 1] << (word_bits - bit_shift)
        } else {
            zero::<T>()
        };
        limbs[i] = lo | hi;
        i += 1;
    }
    HeaplessBigInt {
        limbs,
        len: value.len,
        _p: PhantomData,
    }
}

/// Full-`T` mask from bit 0 of a `black_box`'d choice: `0` when clear, `T::MAX`
/// when set. Mirrors `FixedUInt::const_ct_select` — the `black_box` stops LLVM
/// recognising the XOR-AND-XOR select and rewriting it into a secret-flag
/// conditional move (which asm-grep can't see but ctgrind's taint pass can).
#[inline]
fn ct_mask<T: MachineWord>(choice_bit: u8) -> T {
    let bit = core::hint::black_box(choice_bit & 1);
    let bit_t = <T as core::convert::From<u8>>::from(bit);
    <T as core::ops::Mul>::mul(bit_t, <T as Bounded>::max_value())
}

/// Constant-time left shift by a **secret** `bits`: a branchless barrel
/// shifter, the heapless twin of `FixedUInt::const_shl_ct`. Each public stage
/// `2^k` is applied-or-not via a per-limb masked XOR select on bit `k` of
/// `bits`, so the secret never drives control flow or a memory index. Result
/// width is `value.len` (as `<<`).
pub(crate) fn const_shl_ct<T: MachineWord, const CAP: usize, P: Personality>(
    value: HeaplessBigInt<T, CAP, P>,
    bits: usize,
) -> HeaplessBigInt<T, CAP, P> {
    let n = value.len as usize;
    // `1usize << k` for `k < usize::BITS` stays in range; this covers every
    // amount, over-width ones included (a stage that shifts past the width
    // zeroes the operand, so the select folds to zero). Matches
    // `FixedUInt::const_shl_ct`'s `layers`.
    let layers = core::mem::size_of::<usize>() * 8;
    let mut target = value;
    let mut k = 0;
    while k < layers {
        let shifted = shl_wp(target, 1usize << k);
        let mask = ct_mask::<T>(((bits >> k) & 1) as u8);
        let mut i = 0;
        while i < n {
            let diff = target.limbs[i] ^ shifted.limbs[i];
            target.limbs[i] ^= mask & diff;
            i += 1;
        }
        k += 1;
    }
    target
}

/// Constant-time right shift by a **secret** `bits`: mirror of
/// [`const_shl_ct`] via [`shr_wp`]. Width-preserving (`len == value.len`).
pub(crate) fn const_shr_ct<T: MachineWord, const CAP: usize, P: Personality>(
    value: HeaplessBigInt<T, CAP, P>,
    bits: usize,
) -> HeaplessBigInt<T, CAP, P> {
    let n = value.len as usize;
    let layers = core::mem::size_of::<usize>() * 8;
    let mut target = value;
    let mut k = 0;
    while k < layers {
        let shifted = shr_wp(target, 1usize << k);
        let mask = ct_mask::<T>(((bits >> k) & 1) as u8);
        let mut i = 0;
        while i < n {
            let diff = target.limbs[i] ^ shifted.limbs[i];
            target.limbs[i] ^= mask & diff;
            i += 1;
        }
        k += 1;
    }
    target
}

/// Secret-amount left shift used by `ct_next_pow2`. Thin `u32` wrapper over
/// [`const_shl_ct`].
pub(crate) fn ct_shl<T: MachineWord, const CAP: usize, P: Personality>(
    value: HeaplessBigInt<T, CAP, P>,
    amount: u32,
) -> HeaplessBigInt<T, CAP, P> {
    const_shl_ct(value, amount as usize)
}

// `Shl<u32>` / `Shr<u32>` delegate to the `usize` impls, matching `FixedUInt`.
// The `num_traits` shift traits (`WrappingShl`, `CheckedShl`, …) require these
// as supertraits.
//
// An over-width amount is guarded *before* the `as usize` cast: on a 16-bit
// `usize` target a bare cast of a `u32 >= 2^16` would truncate an over-width
// count into a small in-range one (e.g. `<< 65536` becoming `<< 0`), so we
// short-circuit to the over-width result the `usize` impls would produce
// (`Shl` zeroes at `self.len`, `Shr` empties to len 0). `value_bits()` is a
// `u32`, so the comparison itself never truncates.
impl<T: MachineWord, const CAP: usize, P: Personality> Shl<u32> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn shl(self, bits: u32) -> Self::Output {
        match P::TAG {
            // Ct: the over-width guard would branch on the (secret) amount, so
            // go straight to the barrel — it collapses over-width shifts to
            // zero on its own. `bits as usize` never truncates a meaningful
            // amount (over-width already yields zero).
            PersonalityTag::Ct => const_shl_ct(self, bits as usize),
            PersonalityTag::Nct => {
                let value_bits = self.len as u32 * (core::mem::size_of::<T>() as u32 * 8);
                if bits >= value_bits {
                    Self::new_zero_with_len(self.len())
                } else {
                    self << (bits as usize)
                }
            }
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Shr<u32> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn shr(self, bits: u32) -> Self::Output {
        match P::TAG {
            PersonalityTag::Ct => const_shr_ct(self, bits as usize),
            PersonalityTag::Nct => {
                let value_bits = self.len as u32 * (core::mem::size_of::<T>() as u32 * 8);
                if bits >= value_bits {
                    Self::new_zero_with_len(0)
                } else {
                    self >> (bits as usize)
                }
            }
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Shl<usize> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;

    fn shl(self, bits: usize) -> Self::Output {
        // Ct routes a (possibly secret) amount through the branchless barrel;
        // Nct takes the direct word/bit shift. `P::TAG` is a compile-time
        // constant, so each monomorphisation keeps only its own arm.
        match P::TAG {
            PersonalityTag::Nct => shl_wp(self, bits),
            PersonalityTag::Ct => const_shl_ct(self, bits),
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShlAssign<usize>
    for HeaplessBigInt<T, CAP, P>
{
    fn shl_assign(&mut self, bits: usize) {
        *self = *self << bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShrAssign<usize>
    for HeaplessBigInt<T, CAP, P>
{
    fn shr_assign(&mut self, bits: usize) {
        *self = *self >> bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Shr<usize> for HeaplessBigInt<T, CAP, P> {
    type Output = Self;

    fn shr(self, bits: usize) -> Self::Output {
        match P::TAG {
            // Ct: branchless barrel, width-preserving (a data-dependent `len`
            // shrink would itself leak a secret amount).
            PersonalityTag::Ct => const_shr_ct(self, bits),
            // Nct: direct shift, shrinking `out_len = len - word_shift` (the
            // documented heapless `Shr` width behaviour).
            PersonalityTag::Nct => {
                let word_bits = core::mem::size_of::<T>() * 8;
                let word_shift = bits / word_bits;
                let bit_shift = bits % word_bits;

                let mut limbs = [zero::<T>(); CAP];
                if word_shift >= self.len as usize {
                    return Self {
                        limbs,
                        len: 0,
                        _p: PhantomData,
                    };
                }

                let out_len = self.len as usize - word_shift;

                let mut i = 0;
                while i < out_len {
                    let src_lo = i + word_shift;
                    let lo = self.limbs[src_lo] >> bit_shift;
                    let hi = if bit_shift > 0 && src_lo + 1 < self.len as usize {
                        self.limbs[src_lo + 1] << (word_bits - bit_shift)
                    } else {
                        zero::<T>()
                    };
                    limbs[i] = lo | hi;
                    i += 1;
                }

                Self {
                    limbs,
                    len: out_len as u16,
                    _p: PhantomData,
                }
            }
        }
    }
}

// ── Ref-receiver / ref-RHS operand forms ──
//
// The value `Shl<usize>`/`Shr<usize>` (and their `u32` forms above) carry the
// shift logic; every remaining operand form deref-and-forwards to them.
// `HeaplessBigInt: Copy`, so each deref is a no-op at runtime. This completes
// the same operand matrix `FixedUInt` exposes — receiver ∈ {value, &}, RHS ∈
// {usize, u32, &usize, &u32} — given the value/`usize` and value/`u32` forms.
macro_rules! shift_operand_forms {
    ($imp:ident, $method:ident, $op:tt, $scalar:ty) => {
        impl<T: MachineWord, const CAP: usize, P: Personality> $imp<&$scalar>
            for HeaplessBigInt<T, CAP, P>
        {
            type Output = HeaplessBigInt<T, CAP, P>;
            fn $method(self, bits: &$scalar) -> Self::Output {
                self $op *bits
            }
        }

        impl<T: MachineWord, const CAP: usize, P: Personality> $imp<$scalar>
            for &HeaplessBigInt<T, CAP, P>
        {
            type Output = HeaplessBigInt<T, CAP, P>;
            fn $method(self, bits: $scalar) -> Self::Output {
                *self $op bits
            }
        }

        impl<T: MachineWord, const CAP: usize, P: Personality> $imp<&$scalar>
            for &HeaplessBigInt<T, CAP, P>
        {
            type Output = HeaplessBigInt<T, CAP, P>;
            fn $method(self, bits: &$scalar) -> Self::Output {
                *self $op *bits
            }
        }
    };
}

shift_operand_forms!(Shl, shl, <<, usize);
shift_operand_forms!(Shl, shl, <<, u32);
shift_operand_forms!(Shr, shr, >>, usize);
shift_operand_forms!(Shr, shr, >>, u32);

// Assign forms. `ShlAssign<usize>`/`ShrAssign<usize>` are hand-written above;
// these add the `u32`, `&usize`, and `&u32` RHS variants so `x <<= n` accepts
// the same amounts as `x << n`.
impl<T: MachineWord, const CAP: usize, P: Personality> ShlAssign<u32>
    for HeaplessBigInt<T, CAP, P>
{
    fn shl_assign(&mut self, bits: u32) {
        *self = *self << bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShrAssign<u32>
    for HeaplessBigInt<T, CAP, P>
{
    fn shr_assign(&mut self, bits: u32) {
        *self = *self >> bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShlAssign<&usize>
    for HeaplessBigInt<T, CAP, P>
{
    fn shl_assign(&mut self, bits: &usize) {
        *self = *self << *bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShrAssign<&usize>
    for HeaplessBigInt<T, CAP, P>
{
    fn shr_assign(&mut self, bits: &usize) {
        *self = *self >> *bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShlAssign<&u32>
    for HeaplessBigInt<T, CAP, P>
{
    fn shl_assign(&mut self, bits: &u32) {
        *self = *self << *bits;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ShrAssign<&u32>
    for HeaplessBigInt<T, CAP, P>
{
    fn shr_assign(&mut self, bits: &u32) {
        *self = *self >> *bits;
    }
}

#[cfg(test)]
mod ct_shl_tests {
    use super::{HeaplessBigInt, ct_shl};
    use const_num_traits::{Ct, Nct};

    type HC = HeaplessBigInt<u8, 4, Ct>; // 32-bit width
    type HN = HeaplessBigInt<u8, 4, Nct>;

    #[test]
    fn ct_shl_matches_plain_shift_all_amounts() {
        // The barrel shifter must produce the same value as the (leaky) `<<`
        // for every amount, including over-width (both yield 0 at the width).
        for &raw in &[1u32, 0x1234_5678, 0xFFFF_FFFF, 0x8000_0000] {
            let v = HC::from(raw);
            for amount in 0u32..=40 {
                assert_eq!(
                    ct_shl(v, amount),
                    v << (amount as usize),
                    "ct_shl({raw:#x}, {amount})"
                );
            }
        }
    }

    // The Ct barrels (`const_shl_ct` / `const_shr_ct`) must produce the same
    // VALUE as the Nct reference shift at the full operand width — only timing
    // differs. The CT fixtures check the barrels are branchless, not that they
    // compute the right answer, so pin correctness here across both directions
    // and all amounts (including over-width, which yields 0). `all_limbs`
    // compares the full array, so the Ct width-preserving `>>` and the Nct
    // len-shrinking `>>` still match limb-for-limb via the zero tail.
    #[test]
    fn ct_shifts_match_nct_reference() {
        let cases = [
            [1u8, 0, 0, 0],
            [0x78, 0x56, 0x34, 0x12],
            [0xFF, 0xFF, 0xFF, 0xFF],
            [0, 0, 0, 0x80],
        ];
        for a in cases {
            for amount in 0usize..=40 {
                assert_eq!(
                    (HC::from_limbs(a, 4) << amount).all_limbs(),
                    (HN::from_limbs(a, 4) << amount).all_limbs(),
                    "shl {a:?} << {amount}"
                );
                assert_eq!(
                    (HC::from_limbs(a, 4) >> amount).all_limbs(),
                    (HN::from_limbs(a, 4) >> amount).all_limbs(),
                    "shr {a:?} >> {amount}"
                );
            }
        }
    }
}
