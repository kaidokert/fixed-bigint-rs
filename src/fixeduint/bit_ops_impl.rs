use super::{FixedUInt, MachineWord, const_shl_ct, const_shl_impl, const_shr_ct, const_shr_impl};

use crate::machineword::ConstMachineWord;
use const_num_traits::{
    CheckedShl, CheckedShr, ConstZero, OverflowingShl, OverflowingShr, UnboundedShl, UnboundedShr,
    WrappingShl, WrappingShr,
};
use const_num_traits::{Nct, Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Not for FixedUInt<T, N, P> {
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

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitAnd<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
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

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitAnd for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitand(self, other: Self) -> Self::Output {
            (&self).bitand(&other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitAnd<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitand(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            (&self).bitand(other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitAnd<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitand(self, other: FixedUInt<T, N, P>) -> Self::Output {
            self.bitand(&other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitAndAssign for FixedUInt<T, N, P> {
        fn bitand_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] &= other.array[i];
                i += 1;
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitOr<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
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

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitOr for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitor(self, other: Self) -> Self::Output {
            (&self).bitor(&other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitOr<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitor(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            (&self).bitor(other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitOr<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitor(self, other: FixedUInt<T, N, P>) -> Self::Output {
            self.bitor(&other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitOrAssign for FixedUInt<T, N, P> {
        fn bitor_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] |= other.array[i];
                i += 1;
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitXor<&FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
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

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitXor for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitxor(self, other: Self) -> Self::Output {
            (&self).bitxor(&other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitXor<&FixedUInt<T, N, P>> for FixedUInt<T, N, P> {
        type Output = Self;
        fn bitxor(self, other: &FixedUInt<T, N, P>) -> Self::Output {
            (&self).bitxor(other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitXor<FixedUInt<T, N, P>> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn bitxor(self, other: FixedUInt<T, N, P>) -> Self::Output {
            self.bitxor(&other)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::BitXorAssign for FixedUInt<T, N, P> {
        fn bitxor_assign(&mut self, other: Self) {
            let mut i = 0;
            while i < N {
                self.array[i] ^= other.array[i];
                i += 1;
            }
        }
    }

    // Primary Shl/Shr implementations
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<usize> for FixedUInt<T, N, P> {
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

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<usize> for FixedUInt<T, N, P> {
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

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shl(self, bits: u32) -> Self::Output {
            const_unbounded_shl_u32(self, bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shr(self, bits: u32) -> Self::Output {
            const_unbounded_shr_u32(self, bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<&usize> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shl(self, bits: &usize) -> Self::Output {
            self.shl(*bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<&usize> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shr(self, bits: &usize) -> Self::Output {
            self.shr(*bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<&u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shl(self, bits: &u32) -> Self::Output {
            self.shl(*bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<&u32> for FixedUInt<T, N, P> {
        type Output = Self;
        fn shr(self, bits: &u32) -> Self::Output {
            self.shr(*bits)
        }
    }

    // Shl/Shr for &FixedUInt
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: usize) -> Self::Output {
            FixedUInt::from_array(self.array).shl(bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: usize) -> Self::Output {
            FixedUInt::from_array(self.array).shr(bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: u32) -> Self::Output {
            FixedUInt::from_array(self.array).shl(bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: u32) -> Self::Output {
            FixedUInt::from_array(self.array).shr(bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<&usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: &usize) -> Self::Output {
            FixedUInt::from_array(self.array).shl(*bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<&usize> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: &usize) -> Self::Output {
            FixedUInt::from_array(self.array).shr(*bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shl<&u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl(self, bits: &u32) -> Self::Output {
            FixedUInt::from_array(self.array).shl(*bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::Shr<&u32> for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr(self, bits: &u32) -> Self::Output {
            FixedUInt::from_array(self.array).shr(*bits)
        }
    }

    // ShlAssign/ShrAssign
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::ShlAssign<usize> for FixedUInt<T, N, P> {
        fn shl_assign(&mut self, bits: usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shl_impl(self, bits),
                PersonalityTag::Ct => const_shl_ct(self, bits),
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::ShrAssign<usize> for FixedUInt<T, N, P> {
        fn shr_assign(&mut self, bits: usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shr_impl(self, bits),
                PersonalityTag::Ct => const_shr_ct(self, bits),
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::ShlAssign<&usize> for FixedUInt<T, N, P> {
        fn shl_assign(&mut self, bits: &usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shl_impl(self, *bits),
                PersonalityTag::Ct => const_shl_ct(self, *bits),
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> core::ops::ShrAssign<&usize> for FixedUInt<T, N, P> {
        fn shr_assign(&mut self, bits: &usize) {
            match P::TAG {
                PersonalityTag::Nct => const_shr_impl(self, *bits),
                PersonalityTag::Ct => const_shr_ct(self, *bits),
            }
        }
    }

    // Shared body for `Shl<u32>` and `UnboundedShl::unbounded_shl`:
    // shift by a u32 amount, with values outside [0, BIT_SIZE) collapsing
    // to zero. Centralizing keeps the two entry points in sync.
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

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> OverflowingShl for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn overflowing_shl(self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shl::<usize>::shl(self, shift);
            (res, overflow)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> OverflowingShr for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn overflowing_shr(self, bits: u32) -> (Self, bool) {
            let (shift, overflow) = normalize_shift_amount(bits, Self::BIT_SIZE);
            let res = core::ops::Shr::<usize>::shr(self, shift);
            (res, overflow)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingShl for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn wrapping_shl(self, bits: u32) -> Self {
            OverflowingShl::overflowing_shl(self, bits).0
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingShr for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn wrapping_shr(self, bits: u32) -> Self {
            OverflowingShr::overflowing_shr(self, bits).0
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedShl for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn checked_shl(self, bits: u32) -> Option<Self> {
            let (res, overflow) = OverflowingShl::overflowing_shl(self, bits);
            if overflow { None } else { Some(res) }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedShr for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn checked_shr(self, bits: u32) -> Option<Self> {
            let (res, overflow) = OverflowingShr::overflowing_shr(self, bits);
            if overflow { None } else { Some(res) }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> UnboundedShl for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn unbounded_shl(self, rhs: u32) -> Self {
            const_unbounded_shl_u32(self, rhs)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> UnboundedShr for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn unbounded_shr(self, rhs: u32) -> Self {
            const_unbounded_shr_u32(self, rhs)
        }
    }

    // --- Reference-receiver shift impls (see add_sub_impl.rs for rationale) ---
    //
    // Output comes from the operator supertrait (`Shl<u32>` / `Shr<u32>`
    // for `&FixedUInt`, defined earlier in this c0nst! block), so
    // Output resolves to `FixedUInt<T,N,P>`.

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> OverflowingShl for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn overflowing_shl(self, bits: u32) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as OverflowingShl>::overflowing_shl(FixedUInt::from_array(self.array), bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> OverflowingShr for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn overflowing_shr(self, bits: u32) -> (FixedUInt<T, N, P>, bool) {
            <FixedUInt<T, N, P> as OverflowingShr>::overflowing_shr(FixedUInt::from_array(self.array), bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingShl for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn wrapping_shl(self, bits: u32) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as WrappingShl>::wrapping_shl(FixedUInt::from_array(self.array), bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> WrappingShr for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn wrapping_shr(self, bits: u32) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as WrappingShr>::wrapping_shr(FixedUInt::from_array(self.array), bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedShl for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn checked_shl(self, bits: u32) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as CheckedShl>::checked_shl(FixedUInt::from_array(self.array), bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> CheckedShr for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn checked_shr(self, bits: u32) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as CheckedShr>::checked_shr(FixedUInt::from_array(self.array), bits)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> UnboundedShl for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn unbounded_shl(self, rhs: u32) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as UnboundedShl>::unbounded_shl(FixedUInt::from_array(self.array), rhs)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> UnboundedShr for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn unbounded_shr(self, rhs: u32) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as UnboundedShr>::unbounded_shr(FixedUInt::from_array(self.array), rhs)
        }
    }

    // --- HighestOne / LowestOne ---------------------------------------------
    //
    // Indices of the highest / lowest set bit. Both reduce to the leading-
    // and trailing-zero counts we already compute (Nct fast-path through
    // `const_leading_zeros` / `const_trailing_zeros`; Ct path through the
    // mask-select `_ct` variants).
    //
    // NOTE: NOT constant-time on a `FixedUInt<_, _, Ct>` carrier — the
    // `Option` return shape leaks whether `self == 0` regardless of what
    // the caller does with the value. Ct callers whose input might be
    // zero should mask it separately (`CtIsZero::ct_is_zero`) before
    // consulting these methods, or avoid them entirely.

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::HighestOne for FixedUInt<T, N, P> {
        fn highest_one(self) -> Option<u32> {
            let lz = <Self as const_num_traits::PrimBits>::leading_zeros(self);
            if lz as usize == Self::BIT_SIZE {
                None
            } else {
                Some(Self::BIT_SIZE as u32 - 1 - lz)
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::LowestOne for FixedUInt<T, N, P> {
        fn lowest_one(self) -> Option<u32> {
            let tz = <Self as const_num_traits::PrimBits>::trailing_zeros(self);
            if tz as usize == Self::BIT_SIZE {
                None
            } else {
                Some(tz)
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::HighestOne for &FixedUInt<T, N, P> {
        fn highest_one(self) -> Option<u32> {
            <FixedUInt<T, N, P> as const_num_traits::HighestOne>::highest_one(FixedUInt::from_array(self.array))
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::LowestOne for &FixedUInt<T, N, P> {
        fn lowest_one(self) -> Option<u32> {
            <FixedUInt<T, N, P> as const_num_traits::LowestOne>::lowest_one(FixedUInt::from_array(self.array))
        }
    }

    // --- BitWidth ----------------------------------------------------------
    //
    // Minimum bits to represent self: `BIT_SIZE - leading_zeros(self)`.
    // Returns 0 for 0. Mirrors std's `u32::BITS - n.leading_zeros()`.

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::BitWidth for FixedUInt<T, N, P> {
        fn bit_width(self) -> u32 {
            Self::BIT_SIZE as u32 - <Self as const_num_traits::PrimBits>::leading_zeros(self)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::BitWidth for &FixedUInt<T, N, P> {
        fn bit_width(self) -> u32 {
            <FixedUInt<T, N, P> as const_num_traits::BitWidth>::bit_width(FixedUInt::from_array(self.array))
        }
    }

    // --- BitsPrecision -----------------------------------------------------
    //
    // Operating width: for a fixed carrier this is `BIT_SIZE` (= N·word_bits),
    // value-independent — width == capacity for FixedUInt. Contrast BitWidth
    // (bit-length, per-value).

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::BitsPrecision for FixedUInt<T, N, P> {
        fn bits_precision(self) -> u32 {
            Self::BIT_SIZE as u32
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::BitsPrecision for &FixedUInt<T, N, P> {
        fn bits_precision(self) -> u32 {
            FixedUInt::<T, N, P>::BIT_SIZE as u32
        }
    }

    // --- IsolateHighestOne / IsolateLowestOne ------------------------------
    //
    // Mask the value down to just its highest / lowest set bit.
    // IsolateHighestOne: `0` → `0`, else `1 << (BIT_SIZE - 1 - leading_zeros)`.
    // IsolateLowestOne: the classic `self & self.wrapping_neg()` trick
    //   (which yields 0 for 0 input automatically) — and uses arithmetic
    //   already implemented uniformly across personalities.

    // NOTE: `isolate_highest_one` is NOT constant-time for FixedUInt under
    // Ct. The `if lz as usize == Self::BIT_SIZE` branch is value-dependent
    // (it leaks whether `self == 0`), and the `pos`-parameterized shift's
    // bit-count is value-dependent too. `IsolateLowestOne` below uses the
    // `self & (0 - self)` trick and IS branchless; callers needing a
    // constant-time highest-bit isolation on a Ct carrier should mask
    // through a different path.
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::IsolateHighestOne for FixedUInt<T, N, P> {
        type Output = Self;
        fn isolate_highest_one(self) -> Self {
            let lz = <Self as const_num_traits::PrimBits>::leading_zeros(self);
            if lz as usize == Self::BIT_SIZE {
                // self == 0; preserve the zero.
                <Self as const_num_traits::ConstZero>::ZERO
            } else {
                let pos = Self::BIT_SIZE as u32 - 1 - lz;
                <Self as const_num_traits::ConstOne>::ONE << (pos as usize)
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::IsolateLowestOne for FixedUInt<T, N, P> {
        type Output = Self;
        fn isolate_lowest_one(self) -> Self {
            // `self & (-self)`. For unsigned `-x` is `wrapping_neg(x) =
            // (0).wrapping_sub(x)`. Works for `self == 0` (0 & 0 = 0).
            let neg = <Self as const_num_traits::WrappingSub>::wrapping_sub(
                <Self as const_num_traits::ConstZero>::ZERO,
                self,
            );
            self & neg
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::IsolateHighestOne for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn isolate_highest_one(self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as const_num_traits::IsolateHighestOne>::isolate_highest_one(FixedUInt::from_array(self.array))
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::IsolateLowestOne for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn isolate_lowest_one(self) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as const_num_traits::IsolateLowestOne>::isolate_lowest_one(FixedUInt::from_array(self.array))
        }
    }

    // --- ShlExact / ShrExact -----------------------------------------------
    //
    // Reversible (lossless) shifts: return `None` if any one-bit would be
    // shifted out, or `rhs >= BIT_SIZE`. Mirrors core's primitive impls
    // exactly (compare `rhs` against `leading_zeros` / `trailing_zeros`).
    //
    // NOTE: NOT constant-time on a `FixedUInt<_, _, Ct>` carrier — the
    // `Option` return shape leaks a range predicate on
    // `leading_zeros(self)` / `trailing_zeros(self)`, i.e. the bit-width
    // of the secret. Ct callers wanting exact shifts should either avoid
    // this trait or gate on their own precondition before calling.

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::ShlExact for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl_exact(self, rhs: u32) -> Option<Self> {
            if (rhs as usize) < Self::BIT_SIZE
                && rhs <= <Self as const_num_traits::PrimBits>::leading_zeros(self)
            {
                Some(self << (rhs as usize))
            } else {
                None
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::ShrExact for FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr_exact(self, rhs: u32) -> Option<Self> {
            if (rhs as usize) < Self::BIT_SIZE
                && rhs <= <Self as const_num_traits::PrimBits>::trailing_zeros(self)
            {
                Some(self >> (rhs as usize))
            } else {
                None
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::ShlExact for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shl_exact(self, rhs: u32) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as const_num_traits::ShlExact>::shl_exact(FixedUInt::from_array(self.array), rhs)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::ShrExact for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn shr_exact(self, rhs: u32) -> Option<FixedUInt<T, N, P>> {
            <FixedUInt<T, N, P> as const_num_traits::ShrExact>::shr_exact(FixedUInt::from_array(self.array), rhs)
        }
    }

    // --- FunnelShl / FunnelShr ---------------------------------------------
    //
    // Double-width funnel shift: form the conceptual `(hi, lo)` value of
    // width `2 * BIT_SIZE`, shift by `n`, and return one half. `n` is a
    // public parameter (loop counters, fixed amounts), so the `n >= BIT_SIZE`
    // panic is value-independent and safe for both personalities. The shift
    // ops dispatched by `<<` / `>>` are personality-aware (Ct uses the
    // mask-AND-XOR variant), so the funnel impl inherits that.

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::FunnelShl for FixedUInt<T, N, P> {
        type Output = Self;
        fn funnel_shl(self, rhs: Self, n: u32) -> Self {
            assert!((n as usize) < Self::BIT_SIZE, "FixedUInt::funnel_shl: n out of range");
            if n == 0 {
                self
            } else {
                let lo_shift = Self::BIT_SIZE as u32 - n;
                (self << (n as usize)) | (rhs >> (lo_shift as usize))
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::FunnelShr for FixedUInt<T, N, P> {
        type Output = Self;
        fn funnel_shr(self, rhs: Self, n: u32) -> Self {
            assert!((n as usize) < Self::BIT_SIZE, "FixedUInt::funnel_shr: n out of range");
            if n == 0 {
                rhs
            } else {
                let hi_shift = Self::BIT_SIZE as u32 - n;
                (rhs >> (n as usize)) | (self << (hi_shift as usize))
            }
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::FunnelShl for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn funnel_shl(self, rhs: Self, n: u32) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as const_num_traits::FunnelShl>::funnel_shl(FixedUInt::from_array(self.array), FixedUInt::from_array(rhs.array), n)
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> const_num_traits::FunnelShr for &FixedUInt<T, N, P> {
        type Output = FixedUInt<T, N, P>;
        fn funnel_shr(self, rhs: Self, n: u32) -> FixedUInt<T, N, P> {
            <FixedUInt<T, N, P> as const_num_traits::FunnelShr>::funnel_shr(FixedUInt::from_array(self.array), FixedUInt::from_array(rhs.array), n)
        }
    }

    // --- DepositBits / ExtractBits (PDEP / PEXT) ---------------------------
    //
    // Nct-only: the natural implementation iterates once per set bit of the
    // mask, which is value-dependent. A constant-time version would have to
    // iterate `BIT_SIZE` times unconditionally (and mask-select per step),
    // which is a worthwhile but separate Ct-fixture exercise. For now we
    // gate on `P = Nct`, matching how `CheckedDiv`/`CheckedRem` and the
    // `Strict*` family are gated.

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> const_num_traits::DepositBits for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn deposit_bits(self, mask: Self) -> Self {
            // Scatter contiguous low bits of `self` into positions of the
            // one-bits of `mask`. Iterates once per set bit of `mask`.
            let mut result = <Self as const_num_traits::ConstZero>::ZERO;
            let mut remaining = mask;
            let mut bb = <Self as const_num_traits::ConstOne>::ONE;
            while !<Self as const_num_traits::Zero>::is_zero(&remaining) {
                // Lowest set bit of `remaining` via `x & -x`.
                let lowest = <Self as const_num_traits::IsolateLowestOne>::isolate_lowest_one(remaining);
                if !<Self as const_num_traits::Zero>::is_zero(&(self & bb)) {
                    result |= lowest;
                }
                remaining = remaining & <Self as const_num_traits::WrappingSub>::wrapping_sub(
                    remaining,
                    <Self as const_num_traits::ConstOne>::ONE,
                );
                bb = <Self as const_num_traits::WrappingShl>::wrapping_shl(bb, 1);
            }
            result
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> const_num_traits::ExtractBits for FixedUInt<T, N, Nct> {
        type Output = Self;
        fn extract_bits(self, mask: Self) -> Self {
            // Gather the bits of `self` selected by `mask` into the low end
            // of the result. Mirror of `deposit_bits`.
            let mut result = <Self as const_num_traits::ConstZero>::ZERO;
            let mut remaining = mask;
            let mut bb = <Self as const_num_traits::ConstOne>::ONE;
            while !<Self as const_num_traits::Zero>::is_zero(&remaining) {
                let lowest = <Self as const_num_traits::IsolateLowestOne>::isolate_lowest_one(remaining);
                if !<Self as const_num_traits::Zero>::is_zero(&(self & lowest)) {
                    result |= bb;
                }
                remaining = remaining & <Self as const_num_traits::WrappingSub>::wrapping_sub(
                    remaining,
                    <Self as const_num_traits::ConstOne>::ONE,
                );
                bb = <Self as const_num_traits::WrappingShl>::wrapping_shl(bb, 1);
            }
            result
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> const_num_traits::DepositBits for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn deposit_bits(self, mask: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as const_num_traits::DepositBits>::deposit_bits(FixedUInt::from_array(self.array), FixedUInt::from_array(mask.array))
        }
    }

    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> const_num_traits::ExtractBits for &FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;
        fn extract_bits(self, mask: Self) -> FixedUInt<T, N, Nct> {
            <FixedUInt<T, N, Nct> as const_num_traits::ExtractBits>::extract_bits(FixedUInt::from_array(self.array), FixedUInt::from_array(mask.array))
        }
    }
}

// num_traits wrappers - delegate to const impls
#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingShl
    for FixedUInt<T, N, P>
{
    fn wrapping_shl(&self, bits: u32) -> Self {
        <&Self as WrappingShl>::wrapping_shl(self, bits)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::WrappingShr
    for FixedUInt<T, N, P>
{
    fn wrapping_shr(&self, bits: u32) -> Self {
        <&Self as WrappingShr>::wrapping_shr(self, bits)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedShl for FixedUInt<T, N, P> {
    fn checked_shl(&self, bits: u32) -> Option<Self> {
        <&Self as CheckedShl>::checked_shl(self, bits)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize, P: Personality> num_traits::CheckedShr for FixedUInt<T, N, P> {
    fn checked_shr(&self, bits: u32) -> Option<Self> {
        <&Self as CheckedShr>::checked_shr(self, bits)
    }
}

#[cfg(test)]
// Coverage tests deliberately exercise every ref/value combination of
// the bitwise/shift operators (see `test_*_combinations`).
#[allow(clippy::op_ref)]
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
    #[cfg(feature = "num-traits")]
    fn test_num_traits_shift_wrappers() {
        use num_traits::{CheckedShl, CheckedShr, WrappingShl, WrappingShr};

        type TestInt = FixedUInt<u8, 2>;

        let a = TestInt::from(1u8);

        // num_traits::WrappingShl is by-ref (upstream signature).
        assert_eq!(WrappingShl::wrapping_shl(&a, 4), TestInt::from(16u8));
        assert_eq!(WrappingShl::wrapping_shl(&a, 16), a); // wraps

        // num_traits::WrappingShr
        let b = TestInt::from(16u8);
        assert_eq!(WrappingShr::wrapping_shr(&b, 4), TestInt::from(1u8));

        // num_traits::CheckedShl
        assert_eq!(CheckedShl::checked_shl(&a, 4), Some(TestInt::from(16u8)));
        assert_eq!(CheckedShl::checked_shl(&a, 16), None);

        // num_traits::CheckedShr
        assert_eq!(CheckedShr::checked_shr(&b, 4), Some(TestInt::from(1u8)));
        assert_eq!(CheckedShr::checked_shr(&b, 16), None);
    }

    #[test]
    fn test_unbounded_shift() {
        type U16 = FixedUInt<u8, 2>;

        let one = U16::from(1u8);

        // Normal shifts (within bounds)
        assert_eq!(UnboundedShl::unbounded_shl(one, 0), one);
        assert_eq!(UnboundedShl::unbounded_shl(one, 4), U16::from(16u8));
        assert_eq!(UnboundedShl::unbounded_shl(one, 15), U16::from(0x8000u16));

        assert_eq!(UnboundedShr::unbounded_shr(U16::from(0x8000u16), 15), one);
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
        assert_eq!(UnboundedShl::unbounded_shl(one32, 32), U32::from(0u8));
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
            T: UnboundedShl<Output = T> + UnboundedShr<Output = T> + Eq + core::fmt::Debug + Copy,
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

    #[test]
    fn test_bit_width() {
        use const_num_traits::BitWidth;
        type U16 = FixedUInt<u8, 2>;
        assert_eq!(BitWidth::bit_width(U16::from(0u8)), 0);
        assert_eq!(BitWidth::bit_width(U16::from(1u8)), 1);
        assert_eq!(BitWidth::bit_width(U16::from(2u8)), 2);
        assert_eq!(BitWidth::bit_width(U16::from(3u8)), 2);
        assert_eq!(BitWidth::bit_width(U16::from(255u8)), 8);
        assert_eq!(BitWidth::bit_width(U16::from(256u16)), 9);
        assert_eq!(BitWidth::bit_width(U16::from(0xFFFFu16)), 16);
    }

    #[test]
    fn test_bits_precision() {
        use const_num_traits::BitsPrecision;
        // Fixed carrier: width == BIT_SIZE, value-independent (= capacity).
        type U16 = FixedUInt<u8, 2>;
        type U32 = FixedUInt<u32, 1>;
        assert_eq!(BitsPrecision::bits_precision(U16::from(0u8)), 16);
        assert_eq!(BitsPrecision::bits_precision(U16::from(0xFFFFu16)), 16);
        assert_eq!(BitsPrecision::bits_precision(U32::from(0u8)), 32);
        assert_eq!(BitsPrecision::bits_precision(&U32::from(7u8)), 32);
    }

    #[test]
    fn test_highest_lowest_one() {
        use const_num_traits::{HighestOne, LowestOne};
        type U16 = FixedUInt<u8, 2>;
        assert_eq!(HighestOne::highest_one(U16::from(0u8)), None);
        assert_eq!(HighestOne::highest_one(U16::from(1u8)), Some(0));
        assert_eq!(HighestOne::highest_one(U16::from(0b1010_0000u8)), Some(7));
        assert_eq!(HighestOne::highest_one(U16::from(0x8000u16)), Some(15));

        assert_eq!(LowestOne::lowest_one(U16::from(0u8)), None);
        assert_eq!(LowestOne::lowest_one(U16::from(1u8)), Some(0));
        assert_eq!(LowestOne::lowest_one(U16::from(0b0010_1000u8)), Some(3));
        assert_eq!(LowestOne::lowest_one(U16::from(0x8000u16)), Some(15));
    }

    #[test]
    fn test_isolate_highest_lowest_one() {
        use const_num_traits::{IsolateHighestOne, IsolateLowestOne};
        type U16 = FixedUInt<u8, 2>;
        // zero → zero
        assert_eq!(
            IsolateHighestOne::isolate_highest_one(U16::from(0u8)),
            U16::from(0u8)
        );
        assert_eq!(
            IsolateLowestOne::isolate_lowest_one(U16::from(0u8)),
            U16::from(0u8)
        );
        // nonzero
        assert_eq!(
            IsolateHighestOne::isolate_highest_one(U16::from(0b1010_0000u8)),
            U16::from(0b1000_0000u8)
        );
        assert_eq!(
            IsolateLowestOne::isolate_lowest_one(U16::from(0b1010_1000u8)),
            U16::from(0b0000_1000u8)
        );
        // power of two: highest == lowest == self
        let p: U16 = U16::from(0x0100u16);
        assert_eq!(IsolateHighestOne::isolate_highest_one(p), p);
        assert_eq!(IsolateLowestOne::isolate_lowest_one(p), p);
    }

    #[test]
    fn test_shl_shr_exact() {
        use const_num_traits::{ShlExact, ShrExact};
        type U16 = FixedUInt<u8, 2>;
        // shl_exact: must not lose bits
        assert_eq!(
            ShlExact::shl_exact(U16::from(1u8), 4),
            Some(U16::from(16u8))
        );
        assert_eq!(ShlExact::shl_exact(U16::from(0u8), 8), Some(U16::from(0u8)));
        // dropping a high bit → None
        assert_eq!(ShlExact::shl_exact(U16::from(0x8000u16), 1), None);
        // rhs >= BIT_SIZE → None
        assert_eq!(ShlExact::shl_exact(U16::from(1u8), 16), None);

        // shr_exact: must not lose set bits
        assert_eq!(
            ShrExact::shr_exact(U16::from(16u8), 4),
            Some(U16::from(1u8))
        );
        assert_eq!(ShrExact::shr_exact(U16::from(0u8), 8), Some(U16::from(0u8)));
        // dropping a low bit → None
        assert_eq!(ShrExact::shr_exact(U16::from(0b0001u8), 1), None);
        assert_eq!(ShrExact::shr_exact(U16::from(0b0011u8), 1), None);
        // rhs >= BIT_SIZE → None
        assert_eq!(ShrExact::shr_exact(U16::from(1u8), 16), None);
    }

    #[test]
    #[allow(clippy::needless_borrows_for_generic_args)]
    fn test_ref_receivers_compile_through() {
        use const_num_traits::{BitWidth, IsolateHighestOne, IsolateLowestOne, ShlExact, ShrExact};
        type U16 = FixedUInt<u8, 2>;
        let v = U16::from(0b0010_1000u8);
        assert_eq!(BitWidth::bit_width(&v), 6);
        assert_eq!(
            IsolateHighestOne::isolate_highest_one(&v),
            U16::from(0b0010_0000u8)
        );
        assert_eq!(
            IsolateLowestOne::isolate_lowest_one(&v),
            U16::from(0b0000_1000u8)
        );
        assert_eq!(ShlExact::shl_exact(&v, 2), Some(U16::from(0b1010_0000u8)));
        assert_eq!(ShrExact::shr_exact(&v, 3), Some(U16::from(0b0000_0101u8)));
    }

    #[test]
    fn test_funnel_shifts() {
        use const_num_traits::{FunnelShl, FunnelShr};
        type U16 = FixedUInt<u8, 2>;

        // 0x0001_8000 << 1 = 0x0003_0000; high half = 0x0003.
        assert_eq!(
            FunnelShl::funnel_shl(U16::from(0x0001u16), U16::from(0x8000u16), 1),
            U16::from(0x0003u16),
        );
        // n == 0: returns self (hi)
        assert_eq!(
            FunnelShl::funnel_shl(U16::from(0xABCDu16), U16::from(0xFFFFu16), 0),
            U16::from(0xABCDu16),
        );
        // 0x0001_8000 >> 1 = 0x0000_C000; low half = 0xC000.
        assert_eq!(
            FunnelShr::funnel_shr(U16::from(0x0001u16), U16::from(0x8000u16), 1),
            U16::from(0xC000u16),
        );
        // n == 0: returns rhs (lo)
        assert_eq!(
            FunnelShr::funnel_shr(U16::from(0xABCDu16), U16::from(0x1234u16), 0),
            U16::from(0x1234u16),
        );

        // Reference receivers
        let hi = U16::from(0x0001u16);
        let lo = U16::from(0x8000u16);
        assert_eq!(FunnelShl::funnel_shl(&hi, &lo, 1), U16::from(0x0003u16));
        assert_eq!(FunnelShr::funnel_shr(&hi, &lo, 1), U16::from(0xC000u16));
    }

    #[test]
    #[should_panic(expected = "funnel_shl: n out of range")]
    fn test_funnel_shl_panics_at_bit_size() {
        use const_num_traits::FunnelShl;
        type U16 = FixedUInt<u8, 2>;
        let _ = FunnelShl::funnel_shl(U16::from(1u8), U16::from(0u8), 16);
    }

    #[test]
    fn test_deposit_extract_bits() {
        use const_num_traits::Nct;
        use const_num_traits::{DepositBits, ExtractBits};
        type U16 = FixedUInt<u8, 2, Nct>;

        // Mirror of the primitive doctest:
        // deposit_bits(0b101, mask=0b1111_0000) = 0b0101_0000
        assert_eq!(
            DepositBits::deposit_bits(U16::from(0b101u8), U16::from(0b1111_0000u8)),
            U16::from(0b0101_0000u8),
        );
        // extract_bits(0b0101_0011, mask=0b1111_0000) = 0b101
        assert_eq!(
            ExtractBits::extract_bits(U16::from(0b0101_0011u8), U16::from(0b1111_0000u8)),
            U16::from(0b101u8),
        );

        // Empty mask → 0 (both directions).
        assert_eq!(
            DepositBits::deposit_bits(U16::from(0xFFFFu16), U16::from(0u8)),
            U16::from(0u8),
        );
        assert_eq!(
            ExtractBits::extract_bits(U16::from(0xFFFFu16), U16::from(0u8)),
            U16::from(0u8),
        );

        // All-ones mask → identity.
        assert_eq!(
            DepositBits::deposit_bits(U16::from(0xABCDu16), U16::from(0xFFFFu16)),
            U16::from(0xABCDu16),
        );
        assert_eq!(
            ExtractBits::extract_bits(U16::from(0xABCDu16), U16::from(0xFFFFu16)),
            U16::from(0xABCDu16),
        );

        // Round-trip on a non-trivial mask. extract then deposit through the
        // same mask gives back the originally-selected bits in their original
        // positions.
        let mask = U16::from(0b1010_1010u8);
        let v = U16::from(0b1111_1111u8);
        let extracted = ExtractBits::extract_bits(v, mask);
        let redeposited = DepositBits::deposit_bits(extracted, mask);
        assert_eq!(redeposited, v & mask);

        // Reference receivers
        let v_ref = U16::from(0b0110_0110u8);
        let m_ref = U16::from(0b1111_0000u8);
        assert_eq!(
            ExtractBits::extract_bits(&v_ref, &m_ref),
            U16::from(0b0110u8),
        );
        assert_eq!(
            DepositBits::deposit_bits(&U16::from(0b101u8), &m_ref),
            U16::from(0b0101_0000u8),
        );
    }

    // --- Empirical const-evaluability proofs ---------------------------------
    //
    // Each trait method below is invoked from a `c0nst fn` wrapper, so the
    // surrounding `c0nst::c0nst!` block forces the compiler to treat it as
    // const-callable when the `nightly` feature is enabled. The
    // `nightly_const_eval_*` tests then bind the wrapper's result to a
    // `const` item — proving the trait method actually evaluates at compile
    // time, not just that the impl is annotated `c0nst`.

    c0nst::c0nst! {
        pub c0nst fn const_overflowing_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> (FixedUInt<T, N, P>, bool) {
            OverflowingShl::overflowing_shl(v, bits)
        }
        pub c0nst fn const_overflowing_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> (FixedUInt<T, N, P>, bool) {
            OverflowingShr::overflowing_shr(v, bits)
        }
        pub c0nst fn const_wrapping_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> FixedUInt<T, N, P> {
            WrappingShl::wrapping_shl(v, bits)
        }
        pub c0nst fn const_wrapping_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> FixedUInt<T, N, P> {
            WrappingShr::wrapping_shr(v, bits)
        }
        pub c0nst fn const_checked_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> Option<FixedUInt<T, N, P>> {
            CheckedShl::checked_shl(v, bits)
        }
        pub c0nst fn const_checked_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> Option<FixedUInt<T, N, P>> {
            CheckedShr::checked_shr(v, bits)
        }
        pub c0nst fn const_unbounded_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> FixedUInt<T, N, P> {
            UnboundedShl::unbounded_shl(v, bits)
        }
        pub c0nst fn const_unbounded_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> FixedUInt<T, N, P> {
            UnboundedShr::unbounded_shr(v, bits)
        }
        pub c0nst fn const_highest_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> Option<u32> {
            const_num_traits::HighestOne::highest_one(v)
        }
        pub c0nst fn const_lowest_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> Option<u32> {
            const_num_traits::LowestOne::lowest_one(v)
        }
        pub c0nst fn const_bit_width<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> u32 {
            const_num_traits::BitWidth::bit_width(v)
        }
        pub c0nst fn const_isolate_highest_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            const_num_traits::IsolateHighestOne::isolate_highest_one(v)
        }
        pub c0nst fn const_isolate_lowest_one<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            const_num_traits::IsolateLowestOne::isolate_lowest_one(v)
        }
        pub c0nst fn const_shl_exact<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> Option<FixedUInt<T, N, P>> {
            const_num_traits::ShlExact::shl_exact(v, bits)
        }
        pub c0nst fn const_shr_exact<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, bits: u32) -> Option<FixedUInt<T, N, P>> {
            const_num_traits::ShrExact::shr_exact(v, bits)
        }
        pub c0nst fn const_funnel_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(hi: FixedUInt<T, N, P>, lo: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            const_num_traits::FunnelShl::funnel_shl(hi, lo, n)
        }
        pub c0nst fn const_funnel_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(hi: FixedUInt<T, N, P>, lo: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            const_num_traits::FunnelShr::funnel_shr(hi, lo, n)
        }
        pub c0nst fn const_deposit_bits<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(v: FixedUInt<T, N, Nct>, mask: FixedUInt<T, N, Nct>) -> FixedUInt<T, N, Nct> {
            const_num_traits::DepositBits::deposit_bits(v, mask)
        }
        pub c0nst fn const_extract_bits<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(v: FixedUInt<T, N, Nct>, mask: FixedUInt<T, N, Nct>) -> FixedUInt<T, N, Nct> {
            const_num_traits::ExtractBits::extract_bits(v, mask)
        }
    }

    #[test]
    fn nightly_const_eval_bit_traits() {
        type U16 = FixedUInt<u8, 2>;

        // Runtime smoke — the wrappers themselves work.
        let v = U16::from(1u8);
        assert_eq!(const_overflowing_shl(v, 4), (U16::from(16u8), false));
        assert_eq!(const_wrapping_shl(v, 4), U16::from(16u8));
        assert_eq!(const_checked_shl(v, 16), None);
        assert_eq!(const_bit_width(U16::from(0xFFu8)), 8);

        // The real proof — evaluate at compile time.
        #[cfg(feature = "nightly")]
        {
            const V: U16 = FixedUInt::from_array([1, 0]);
            const V_FF: U16 = FixedUInt::from_array([0xFF, 0]);
            const V_MASK: U16 = FixedUInt::from_array([0b1010_1000, 0]);
            const HI: U16 = FixedUInt::from_array([1, 0]);
            const LO: U16 = FixedUInt::from_array([0, 0x80]);

            const OSHL: (U16, bool) = const_overflowing_shl(V, 4);
            const OSHR: (U16, bool) = const_overflowing_shr(V_FF, 4);
            const WSHL: U16 = const_wrapping_shl(V, 4);
            const WSHR: U16 = const_wrapping_shr(V_FF, 4);
            const CSHL: Option<U16> = const_checked_shl(V, 16);
            const CSHR: Option<U16> = const_checked_shr(V, 4);
            const USHL: U16 = const_unbounded_shl(V, 8);
            const USHR: U16 = const_unbounded_shr(V_FF, 4);
            const HI_ONE: Option<u32> = const_highest_one(V_FF);
            const LO_ONE: Option<u32> = const_lowest_one(V_MASK);
            const BW: u32 = const_bit_width(V_FF);
            const IH: U16 = const_isolate_highest_one(V_MASK);
            const IL: U16 = const_isolate_lowest_one(V_MASK);
            const SHLEX: Option<U16> = const_shl_exact(V, 4);
            const SHREX: Option<U16> = const_shr_exact(FixedUInt::from_array([16, 0]), 4);
            const FSHL: U16 = const_funnel_shl(HI, LO, 1);
            const FSHR: U16 = const_funnel_shr(HI, LO, 1);
            const DEP: U16 = const_deposit_bits(
                FixedUInt::from_array([0b101, 0]),
                FixedUInt::from_array([0b1111_0000, 0]),
            );
            const EXT: U16 = const_extract_bits(
                FixedUInt::from_array([0b0101_0011, 0]),
                FixedUInt::from_array([0b1111_0000, 0]),
            );

            // Sanity-check a representative subset of the const results.
            assert_eq!(OSHL.0.array, [16, 0]);
            assert!(!OSHL.1);
            assert_eq!(OSHR.0.array, [0x0F, 0]);
            assert!(!OSHR.1);
            assert_eq!(WSHL.array, [16, 0]);
            assert_eq!(WSHR.array, [0x0F, 0]);
            assert!(CSHL.is_none());
            assert!(CSHR.is_some());
            assert_eq!(USHL.array, [0, 1]);
            assert_eq!(USHR.array, [0x0F, 0]);
            assert_eq!(HI_ONE, Some(7));
            assert_eq!(LO_ONE, Some(3));
            assert_eq!(BW, 8);
            assert_eq!(IH.array, [0b1000_0000, 0]);
            assert_eq!(IL.array, [0b0000_1000, 0]);
            assert!(SHLEX.is_some());
            assert!(SHREX.is_some());
            assert_eq!(FSHL.array, [0x03, 0]);
            assert_eq!(FSHR.array, [0x00, 0xC0]);
            assert_eq!(DEP.array, [0b0101_0000, 0]);
            assert_eq!(EXT.array, [0b101, 0]);
        }
    }
}
