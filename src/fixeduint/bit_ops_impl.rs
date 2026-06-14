use super::{const_shl_ct, const_shl_impl, const_shr_ct, const_shr_impl, FixedUInt, MachineWord};

use crate::const_numtraits::{CheckedShl, CheckedShr, ConstZero, One, OverflowingShl, OverflowingShr, UnboundedShl, UnboundedShr, WrappingShl, WrappingShr, Zero};
use crate::machineword::ConstMachineWord;
use crate::personality::{Personality, PersonalityTag};

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Not for FixedUInt<T, N, P> {
        type Output = Self;
        fn not(self) -> Self::Output {
            let mut ret = <Self as ConstZero>::ZERO;
            let mut i = 0;
            while i < N {
                ret.array[i] = !self.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitAnd<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitand(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            let mut ret = <FixedUInt<T, N, P> as ConstZero>::ZERO;
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[i] & other.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitAnd for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitand(self, other: Self) -> Self::Output {
            (&self).bitand(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitAnd<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitand(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            (&self).bitand(other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitAnd<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitand(self, other: FixedUInt<T, N, P>) -> Self::Output {
            self.bitand(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitAndAssign for FixedUInt<T, N, P> {
        fn bitand_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] &= other.array[i];
                i += 1;
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitOr<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitor(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            let mut ret = <FixedUInt<T, N, P> as ConstZero>::ZERO;
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[i] | other.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitOr for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitor(self, other: Self) -> Self::Output {
            (&self).bitor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitOr<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitor(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            (&self).bitor(other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitOr<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitor(self, other: FixedUInt<T, N, P>) -> Self::Output {
            self.bitor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitOrAssign for FixedUInt<T, N, P> {
        fn bitor_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] |= other.array[i];
                i += 1;
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitXor<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitxor(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            let mut ret = <FixedUInt<T, N, P> as ConstZero>::ZERO;
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[i] ^ other.array[i];
                i += 1;
            }
            ret
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitXor for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitxor(self, other: Self) -> Self::Output {
            (&self).bitxor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitXor<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitxor(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            (&self).bitxor(other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitXor<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitxor(self, other: FixedUInt<T, N, P>) -> Self::Output {
            self.bitxor(&other)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::BitXorAssign for FixedUInt<T, N, P> {
        fn bitxor_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] ^= other.array[i];
                i += 1;
            }
        }
    }

    // Primary Shl/Shr implementations
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<usize> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shl(self, bits: usize) -> Self::Output {
            let mut result = self;
            match P::TAG {
                PersonalityTag::Nct => const_shl_impl(&mut result, bits),
                PersonalityTag::Ct => const_shl_ct(&mut result, bits),
            }
            result
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<usize> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shr(self, bits: usize) -> Self::Output {
            let mut result = self;
            match P::TAG {
                PersonalityTag::Nct => const_shr_impl(&mut result, bits),
                PersonalityTag::Ct => const_shr_ct(&mut result, bits),
            }
            result
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shl(self, bits: u32) -> Self::Output {
            const_unbounded_shl_u32(self, bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shr(self, bits: u32) -> Self::Output {
            const_unbounded_shr_u32(self, bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<&usize> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shl(self, bits: &usize) -> Self::Output {
            self.shl(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<&usize> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shr(self, bits: &usize) -> Self::Output {
            self.shr(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<&u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shl(self, bits: &u32) -> Self::Output {
            self.shl(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<&u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shr(self, bits: &u32) -> Self::Output {
            self.shr(*bits)
        }
    }

    // Shl/Shr for &FixedUInt
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: usize) -> Self::Output {
            (*self).shl(bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: usize) -> Self::Output {
            (*self).shr(bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: u32) -> Self::Output {
            (*self).shl(bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: u32) -> Self::Output {
            (*self).shr(bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<&usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: &usize) -> Self::Output {
            (*self).shl(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<&usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: &usize) -> Self::Output {
            (*self).shr(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shl<&u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: &u32) -> Self::Output {
            (*self).shl(*bits)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::Shr<&u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: &u32) -> Self::Output {
            (*self).shr(*bits)
        }
    }

    // ShlAssign/ShrAssign
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::ShlAssign<usize> for FixedUInt<T, N, P> {
        fn shl_assign(&mut self, bits: usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shl_impl(self, bits),
                PersonalityTag::Ct => const_shl_ct(self, bits),
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::ShrAssign<usize> for FixedUInt<T, N, P> {
        fn shr_assign(&mut self, bits: usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shr_impl(self, bits),
                PersonalityTag::Ct => const_shr_ct(self, bits),
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::ShlAssign<&usize> for FixedUInt<T, N, P> {
        fn shl_assign(&mut self, bits: &usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shl_impl(self, *bits),
                PersonalityTag::Ct => const_shl_ct(self, *bits),
            }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst core::ops::ShrAssign<&usize> for FixedUInt<T, N, P> {
        fn shr_assign(&mut self, bits: &usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shr_impl(self, *bits),
                PersonalityTag::Ct => const_shr_ct(self, *bits),
            }
        }
    }

    // Shared body for `Shl<u32>` and `UnboundedShl::unbounded_shl`.
    // Both want the same semantics — shift by a u32 amount, with values
    // outside [0, BIT_SIZE) collapsing to zero — and previously had
    // parallel implementations. The Ct fix in PR #120 was applied to
    // `unbounded_shl` but missed the `Shl<u32>` copy; centralizing here
    // makes that class of drift impossible.
    pub(crate) c0nst fn const_unbounded_shl_u32<
        T: [c0nst] ConstMachineWord + MachineWord,
        const N: usize,
        P: Personality,
    >(
        target: FixedUInt<T, N, P>,
        bits: u32,
    ) -> FixedUInt<T, N, P> {
        match P::TAG {
            PersonalityTag::Nct => {
                let (shift, overflow) =
                    normalize_shift_amount(bits, FixedUInt::<T, N, P>::BIT_SIZE);
                if overflow {
                    <FixedUInt<T, N, P> as ConstZero>::ZERO
                } else {
                    target << shift
                }
            }
            PersonalityTag::Ct => {
                // Skip `normalize_shift_amount` entirely. Its `if bits >=
                // bit_size_u32` is a tainted-flag branch and `bits %
                // bit_size_u32` is a variable-time modulo when bits is a
                // secret — both leaks even though current LLVM may pattern-
                // match them on power-of-2 BIT_SIZE. `const_shl_ct`'s
                // barrel shifter already collapses out-of-range shifts to
                // zero (via `const_shl_impl`'s `nwords >= N` zero-out), so
                // the overflow detection is redundant for the Ct path —
                // EXCEPT for the cast to usize on 16-bit-usize targets,
                // where `bits as usize` truncates and could undo the
                // saturation. Cap branchlessly to `BIT_SIZE` first; for
                // every priority diagonal BIT_SIZE fits in u16, so the
                // capped value casts losslessly even on AVR.
                let bit_size_u32 = FixedUInt::<T, N, P>::BIT_SIZE as u32;
                let capped = const_ct_min_u32(bits, bit_size_u32);
                target << (capped as usize)
            }
        }
    }

    /// Mirror of [`const_unbounded_shl_u32`] for right-shifts.
    pub(crate) c0nst fn const_unbounded_shr_u32<
        T: [c0nst] ConstMachineWord + MachineWord,
        const N: usize,
        P: Personality,
    >(
        target: FixedUInt<T, N, P>,
        bits: u32,
    ) -> FixedUInt<T, N, P> {
        match P::TAG {
            PersonalityTag::Nct => {
                let (shift, overflow) =
                    normalize_shift_amount(bits, FixedUInt::<T, N, P>::BIT_SIZE);
                if overflow {
                    <FixedUInt<T, N, P> as ConstZero>::ZERO
                } else {
                    target >> shift
                }
            }
            PersonalityTag::Ct => {
                // See `const_unbounded_shl_u32` for why this skips
                // `normalize_shift_amount` and caps before casting.
                let bit_size_u32 = FixedUInt::<T, N, P>::BIT_SIZE as u32;
                let capped = const_ct_min_u32(bits, bit_size_u32);
                target >> (capped as usize)
            }
        }
    }

    /// Branchless CT-safe `min(bits, cap)` for u32, used to clamp Ct
    /// shift amounts to `BIT_SIZE` before casting to usize. The
    /// `black_box` on the mask is load-bearing — without it, LLVM
    /// recognises the XOR-AND-XOR select idiom and rewrites it into a
    /// `cmov` whose flag depends on the secret `bits`. Same defence as
    /// `const_ct_select` (PR #118).
    c0nst fn const_ct_min_u32(bits: u32, cap: u32) -> u32 {
        // diff = cap - bits, wraps to negative (high bit set) iff bits > cap.
        let diff = cap.wrapping_sub(bits);
        let too_big_bit = (diff >> 31) & 1;
        let too_big_mask = core::hint::black_box(too_big_bit.wrapping_neg());
        // bits if !too_big, cap otherwise. XOR-AND-XOR select with
        // opaque mask.
        bits ^ (too_big_mask & (bits ^ cap))
    }

    // Helper to normalize shift amount and detect overflow.
    // Handles both 16-bit (usize < u32) and 64-bit (bit_size > u32::MAX) platforms.
    c0nst fn normalize_shift_amount(bits: u32, bit_size: usize) -> (usize, bool) {
        let bit_size_u32 = bit_size as u32;
        if bit_size == 0 {
            // Zero-size type: always overflow
            (0, true)
        } else if bit_size_u32 == 0 {
            // bit_size is a non-zero multiple of 2^32 (huge type on 64-bit).
            // Since bits is u32, it's always smaller than bit_size. No overflow.
            (bits as usize, false)
        } else if bits >= bit_size_u32 {
            // Normal case: shift exceeds bit width
            ((bits % bit_size_u32) as usize, true)
        } else {
            (bits as usize, false)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst OverflowingShl for FixedUInt<T, N, P> {
        fn overflowing_shl(self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shl::<usize>::shl(self, shift);
            (res, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst OverflowingShr for FixedUInt<T, N, P> {
        fn overflowing_shr(self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shr::<usize>::shr(self, shift);
            (res, overflow)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst WrappingShl for FixedUInt<T, N, P> {
        fn wrapping_shl(self, bits: u32) -> Self {
            OverflowingShl::overflowing_shl(self, bits).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst WrappingShr for FixedUInt<T, N, P> {
        fn wrapping_shr(self, bits: u32) -> Self {
            OverflowingShr::overflowing_shr(self, bits).0
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst CheckedShl for FixedUInt<T, N, P> {
        fn checked_shl(self, bits: u32) -> Option<Self> {
            let (res, overflow) = OverflowingShl::overflowing_shl(self, bits);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst CheckedShr for FixedUInt<T, N, P> {
        fn checked_shr(self, bits: u32) -> Option<Self> {
            let (res, overflow) = OverflowingShr::overflowing_shr(self, bits);
            if overflow { None } else { Some(res) }
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst UnboundedShl for FixedUInt<T, N, P> {
        fn unbounded_shl(self, rhs: u32) -> Self {
            const_unbounded_shl_u32(self, rhs)
        }
    }

    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst UnboundedShr for FixedUInt<T, N, P> {
        fn unbounded_shr(self, rhs: u32) -> Self {
            const_unbounded_shr_u32(self, rhs)
        }
    }
}

// num_traits wrappers - delegate to const impls
// (OverflowingShl/OverflowingShr legacy shim impls retired — the const
// impls above ARE the OverflowingShl/Shr impls now that we depend on
// the external const-num-traits crate directly.)
impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingShl
    for FixedUInt<T, N, P>
{
    fn wrapping_shl(&self, bits: u32) -> Self {
        WrappingShl::wrapping_shl(*self, bits)
    }
}

impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingShr
    for FixedUInt<T, N, P>
{
    fn wrapping_shr(&self, bits: u32) -> Self {
        WrappingShr::wrapping_shr(*self, bits)
    }
}

impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedShl for FixedUInt<T, N, P> {
    fn checked_shl(&self, bits: u32) -> Option<Self> {
        CheckedShl::checked_shl(*self, bits)
    }
}

impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedShr for FixedUInt<T, N, P> {
    fn checked_shr(&self, bits: u32) -> Option<Self> {
        CheckedShr::checked_shr(*self, bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitand_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8); // 1100
        let b = FixedUInt::<u8, 2>::from(10u8); // 1010
        let expected = FixedUInt::<u8, 2>::from(8u8); // 1000

        // value & value
        assert_eq!(a & b, expected);
        // value & ref
        assert_eq!(a & &b, expected);
        // ref & value
        assert_eq!(&a & b, expected);
        // ref & ref
        assert_eq!(&a & &b, expected);
    }

    #[test]
    fn test_bitor_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8); // 1100
        let b = FixedUInt::<u8, 2>::from(10u8); // 1010
        let expected = FixedUInt::<u8, 2>::from(14u8); // 1110

        // value | value
        assert_eq!(a | b, expected);
        // value | ref
        assert_eq!(a | &b, expected);
        // ref | value
        assert_eq!(&a | b, expected);
        // ref | ref
        assert_eq!(&a | &b, expected);
    }

    #[test]
    fn test_bitxor_combinations() {
        let a = FixedUInt::<u8, 2>::from(12u8); // 1100
        let b = FixedUInt::<u8, 2>::from(10u8); // 1010
        let expected = FixedUInt::<u8, 2>::from(6u8); // 0110

        // value ^ value
        assert_eq!(a ^ b, expected);
        // value ^ ref
        assert_eq!(a ^ &b, expected);
        // ref ^ value
        assert_eq!(&a ^ b, expected);
        // ref ^ ref
        assert_eq!(&a ^ &b, expected);
    }

    #[test]
    fn test_shl_combinations() {
        let a = FixedUInt::<u8, 2>::from(2u8); // 0010
        let shift: usize = 2;
        let expected = FixedUInt::<u8, 2>::from(8u8); // 1000

        // value << value
        assert_eq!(a << shift, expected);
        // value << ref
        assert_eq!(a << &shift, expected);
        // ref << value
        assert_eq!(&a << shift, expected);
        // ref << ref
        assert_eq!(&a << &shift, expected);

        // Same with u32
        let shift32: u32 = 2;
        assert_eq!(a << shift32, expected);
        assert_eq!(a << &shift32, expected);
        assert_eq!(&a << shift32, expected);
        assert_eq!(&a << &shift32, expected);
    }

    #[test]
    fn test_shr_combinations() {
        let a = FixedUInt::<u8, 2>::from(8u8); // 1000
        let shift: usize = 2;
        let expected = FixedUInt::<u8, 2>::from(2u8); // 0010

        // value >> value
        assert_eq!(a >> shift, expected);
        // value >> ref
        assert_eq!(a >> &shift, expected);
        // ref >> value
        assert_eq!(&a >> shift, expected);
        // ref >> ref
        assert_eq!(&a >> &shift, expected);

        // Same with u32
        let shift32: u32 = 2;
        assert_eq!(a >> shift32, expected);
        assert_eq!(a >> &shift32, expected);
        assert_eq!(&a >> shift32, expected);
        assert_eq!(&a >> &shift32, expected);
    }

    #[test]
    fn test_const_bitops() {
        type TestInt = FixedUInt<u8, 2>;

        let a = TestInt::from(0b11001100u8);
        let b = TestInt::from(0b10101010u8);

        // Test not
        let not_a = !a;
        assert_eq!(not_a.array[0], 0b00110011);
        assert_eq!(not_a.array[1], 0xFF);

        // Test bitand
        assert_eq!(a & b, TestInt::from(0b10001000u8));

        // Test bitor
        assert_eq!(a | b, TestInt::from(0b11101110u8));

        // Test bitxor
        assert_eq!(a ^ b, TestInt::from(0b01100110u8));

        // Test shl
        assert_eq!(TestInt::from(1u8) << 4usize, TestInt::from(16u8));

        // Test shr
        assert_eq!(TestInt::from(16u8) >> 2usize, TestInt::from(4u8));

        #[cfg(feature = "nightly")]
        {
            const A: TestInt = FixedUInt::from_array([0b11001100, 0]);
            const B: TestInt = FixedUInt::from_array([0b10101010, 0]);

            const NOT_A: TestInt = !A;
            const AND_AB: TestInt = A & B;
            const OR_AB: TestInt = A | B;
            const XOR_AB: TestInt = A ^ B;
            const SHL_1: TestInt = FixedUInt::from_array([1u8, 0]) << 4usize;
            const SHR_16: TestInt = FixedUInt::from_array([16u8, 0]) >> 2usize;

            assert_eq!(NOT_A.array[0], 0b00110011);
            assert_eq!(AND_AB.array[0], 0b10001000);
            assert_eq!(OR_AB.array[0], 0b11101110);
            assert_eq!(XOR_AB.array[0], 0b01100110);
            assert_eq!(SHL_1.array[0], 16);
            assert_eq!(SHR_16.array[0], 4);
        }
    }

    #[test]
    fn test_const_shift_traits() {
        type TestInt = FixedUInt<u8, 2>; // 16-bit

        // Test overflowing_shl
        let a = TestInt::from(0x80u8); // 0x0080
        let (res, overflow) = OverflowingShl::overflowing_shl(a, 8);
        assert_eq!(res.array, [0, 0x80]); // 0x8000
        assert!(!overflow);

        let (res, overflow) = OverflowingShl::overflowing_shl(a, 16);
        assert_eq!(res.array, [0x80, 0]); // wraps around
        assert!(overflow);

        let (res, overflow) = OverflowingShl::overflowing_shl(a, 9);
        assert_eq!(res.array, [0, 0]); // high bits shifted out (but shift < bit_width)
        assert!(!overflow); // 9 < 16, so no overflow

        // Test overflowing_shr
        let b = TestInt::from(0x0100u16); // 0x0100
        let (res, overflow) = OverflowingShr::overflowing_shr(b, 8);
        assert_eq!(res.array, [1, 0]); // 0x0001
        assert!(!overflow);

        let (res, overflow) = OverflowingShr::overflowing_shr(b, 16);
        assert_eq!(res.array, [0, 1]); // wraps
        assert!(overflow);

        // Test wrapping_shl
        let c = TestInt::from(1u8);
        assert_eq!(WrappingShl::wrapping_shl(c, 4).array, [16, 0]);
        assert_eq!(WrappingShl::wrapping_shl(c, 16).array, [1, 0]); // wraps
        assert_eq!(WrappingShl::wrapping_shl(c, 17).array, [2, 0]); // wraps

        // Test wrapping_shr
        let d = TestInt::from(0x8000u16);
        assert_eq!(WrappingShr::wrapping_shr(d, 4).array, [0, 0x08]);
        assert_eq!(WrappingShr::wrapping_shr(d, 16).array, [0, 0x80]); // wraps
        assert_eq!(WrappingShr::wrapping_shr(d, 17).array, [0, 0x40]); // wraps

        // Test checked_shl
        let e = TestInt::from(1u8);
        assert_eq!(CheckedShl::checked_shl(e, 4), Some(TestInt::from(16u8)));
        assert_eq!(
            CheckedShl::checked_shl(e, 15),
            Some(TestInt::from(0x8000u16))
        );
        assert_eq!(CheckedShl::checked_shl(e, 16), None); // overflow

        // Test checked_shr
        let f = TestInt::from(0x8000u16);
        assert_eq!(CheckedShr::checked_shr(f, 15), Some(TestInt::from(1u8)));
        assert_eq!(CheckedShr::checked_shr(f, 16), None); // overflow

        // Test edge case: zero shift
        let g = TestInt::from(42u8);
        assert_eq!(OverflowingShl::overflowing_shl(g, 0), (g, false));
        assert_eq!(OverflowingShr::overflowing_shr(g, 0), (g, false));
        assert_eq!(WrappingShl::wrapping_shl(g, 0), g);
        assert_eq!(WrappingShr::wrapping_shr(g, 0), g);
        assert_eq!(CheckedShl::checked_shl(g, 0), Some(g));
        assert_eq!(CheckedShr::checked_shr(g, 0), Some(g));
    }

    #[test]
    fn test_const_shift_traits_n0() {
        // Test with N=0 (zero-sized type)
        type ZeroInt = FixedUInt<u8, 0>;
        let z = ZeroInt::from_array([]);

        // All shifts on zero-sized type should overflow
        assert_eq!(OverflowingShl::overflowing_shl(z, 0), (z, true));
        assert_eq!(OverflowingShr::overflowing_shr(z, 0), (z, true));
        assert_eq!(WrappingShl::wrapping_shl(z, 0), z);
        assert_eq!(WrappingShr::wrapping_shr(z, 0), z);
        assert_eq!(CheckedShl::checked_shl(z, 0), None);
        assert_eq!(CheckedShr::checked_shr(z, 0), None);
    }

    #[test]
    fn test_num_traits_shift_wrappers() {
        use num_traits::{CheckedShl, CheckedShr, WrappingShl, WrappingShr};

        type TestInt = FixedUInt<u8, 2>;

        let a = TestInt::from(1u8);

        // num_traits::WrappingShl delegates to WrappingShl
        assert_eq!(WrappingShl::wrapping_shl(a, 4), TestInt::from(16u8));
        assert_eq!(WrappingShl::wrapping_shl(a, 16), a); // wraps

        // num_traits::WrappingShr
        let b = TestInt::from(16u8);
        assert_eq!(WrappingShr::wrapping_shr(b, 4), TestInt::from(1u8));

        // num_traits::CheckedShl
        assert_eq!(CheckedShl::checked_shl(a, 4), Some(TestInt::from(16u8)));
        assert_eq!(CheckedShl::checked_shl(a, 16), None);

        // num_traits::CheckedShr
        assert_eq!(CheckedShr::checked_shr(b, 4), Some(TestInt::from(1u8)));
        assert_eq!(CheckedShr::checked_shr(b, 16), None);
    }

    #[test]
    fn test_unbounded_shift() {
        type U16 = FixedUInt<u8, 2>;

        let one = U16::from(1u8);

        // Normal shifts (within bounds)
        assert_eq!(UnboundedShl::unbounded_shl(one, 0), one);
        assert_eq!(UnboundedShl::unbounded_shl(one, 4), U16::from(16u8));
        assert_eq!(
            UnboundedShl::unbounded_shl(one, 15),
            U16::from(0x8000u16)
        );

        assert_eq!(
            UnboundedShr::unbounded_shr(U16::from(0x8000u16), 15),
            one
        );
        assert_eq!(UnboundedShr::unbounded_shr(U16::from(16u8), 4), one);

        // At boundary (shift by bit width) - returns 0
        assert_eq!(UnboundedShl::unbounded_shl(one, 16), U16::from(0u8));
        assert_eq!(
            UnboundedShr::unbounded_shr(U16::from(0xFFFFu16), 16),
            U16::from(0u8)
        );

        // Beyond boundary - returns 0
        assert_eq!(
            UnboundedShl::unbounded_shl(U16::from(0xFFFFu16), 17),
            U16::from(0u8)
        );
        assert_eq!(
            UnboundedShl::unbounded_shl(U16::from(0xFFFFu16), 100),
            U16::from(0u8)
        );
        assert_eq!(
            UnboundedShr::unbounded_shr(U16::from(0xFFFFu16), 17),
            U16::from(0u8)
        );
        assert_eq!(
            UnboundedShr::unbounded_shr(U16::from(0xFFFFu16), 100),
            U16::from(0u8)
        );

        // Test with different word sizes
        type U32 = FixedUInt<u8, 4>;
        let one32 = U32::from(1u8);
        assert_eq!(
            UnboundedShl::unbounded_shl(one32, 31),
            U32::from(0x80000000u32)
        );
        assert_eq!(
            UnboundedShl::unbounded_shl(one32, 32),
            U32::from(0u8)
        );
        assert_eq!(
            UnboundedShr::unbounded_shr(U32::from(0x80000000u32), 31),
            one32
        );
        assert_eq!(
            UnboundedShr::unbounded_shr(U32::from(0x80000000u32), 32),
            U32::from(0u8)
        );
    }

    #[test]
    fn test_unbounded_shift_polymorphic() {
        fn test_unbounded<T>(val: T, shift: u32, expected_shl: T, expected_shr: T)
        where
            T: UnboundedShl + Eq + core::fmt::Debug + Copy,
        {
            assert_eq!(UnboundedShl::unbounded_shl(val, shift), expected_shl);
            assert_eq!(UnboundedShr::unbounded_shr(val, shift), expected_shr);
        }

        // Test with FixedUInt layouts
        type U8x2 = FixedUInt<u8, 2>;
        type U8x4 = FixedUInt<u8, 4>;
        type U16x2 = FixedUInt<u16, 2>;

        // Same logical shift, different layouts
        test_unbounded(U8x2::from(1u8), 4, U8x2::from(16u8), U8x2::from(0u8));
        test_unbounded(U8x4::from(1u8), 4, U8x4::from(16u8), U8x4::from(0u8));
        test_unbounded(U16x2::from(1u8), 4, U16x2::from(16u8), U16x2::from(0u8));

        // Test with primitives
        test_unbounded(1u8, 4, 16u8, 0u8);
        test_unbounded(1u16, 4, 16u16, 0u16);
        test_unbounded(1u32, 4, 16u32, 0u32);

        // Boundary tests
        test_unbounded(1u8, 8, 0u8, 0u8);
        test_unbounded(U8x2::from(1u8), 16, U8x2::from(0u8), U8x2::from(0u8));
    }
}
