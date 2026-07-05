use super::{
    FixedUInt, MachineWord, const_leading_zeros, const_leading_zeros_ct, const_trailing_zeros,
    const_trailing_zeros_ct,
};
use crate::machineword::ConstMachineWord;
#[cfg(feature = "num-traits")]
use const_num_traits::One;
use const_num_traits::PrimBits;
use const_num_traits::{Nct, Personality, PersonalityTag};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> PrimBits for FixedUInt<T, N, P> {
        fn count_ones(self) -> u32 {
            let mut count = 0u32;
            let mut i = 0;
            while i < N {
                count += self.array[i].count_ones();
                i += 1;
            }
            count
        }
        fn count_zeros(self) -> u32 {
            let mut count = 0u32;
            let mut i = 0;
            while i < N {
                count += self.array[i].count_zeros();
                i += 1;
            }
            count
        }
        fn leading_zeros(self) -> u32 {
            match P::TAG {
                PersonalityTag::Nct => const_leading_zeros(&self.array),
                PersonalityTag::Ct => const_leading_zeros_ct(&self.array),
            }
        }
        fn trailing_zeros(self) -> u32 {
            match P::TAG {
                PersonalityTag::Nct => const_trailing_zeros(&self.array),
                PersonalityTag::Ct => const_trailing_zeros_ct(&self.array),
            }
        }
        fn swap_bytes(self) -> Self {
            let mut ret = <Self as const_num_traits::ConstZero>::ZERO;
            let mut i = 0;
            while i < N {
                ret.array[i] = self.array[N - 1 - i].swap_bytes();
                i += 1;
            }
            ret
        }
        fn rotate_left(self, n: u32) -> Self {
            let bit_size = Self::BIT_SIZE as u32;
            if bit_size == 0 {
                return self;
            }
            let shift = n % bit_size;
            let a = core::ops::Shl::<u32>::shl(self, shift);
            let b = core::ops::Shr::<u32>::shr(self, bit_size - shift);
            core::ops::BitOr::bitor(a, b)
        }
        fn rotate_right(self, n: u32) -> Self {
            let bit_size = Self::BIT_SIZE as u32;
            if bit_size == 0 {
                return self;
            }
            let shift = n % bit_size;
            let a = core::ops::Shr::<u32>::shr(self, shift);
            let b = core::ops::Shl::<u32>::shl(self, bit_size - shift);
            core::ops::BitOr::bitor(a, b)
        }
        fn unsigned_shl(self, n: u32) -> Self {
            core::ops::Shl::<u32>::shl(self, n)
        }
        fn unsigned_shr(self, n: u32) -> Self {
            core::ops::Shr::<u32>::shr(self, n)
        }
        fn signed_shl(self, n: u32) -> Self {
            // FixedUInt is always unsigned, so signed_shl is equivalent
            // to unsigned_shl (the sign bit doesn't change shift-left
            // semantics for unsigned types).
            core::ops::Shl::<u32>::shl(self, n)
        }
        fn signed_shr(self, n: u32) -> Self {
            // For unsigned types the sign bit is always 0, so the
            // arithmetic (sign-extending) right shift produces the
            // same result as the logical right shift.
            core::ops::Shr::<u32>::shr(self, n)
        }
        fn reverse_bits(self) -> Self {
            let mut ret = <Self as const_num_traits::ConstZero>::ZERO;
            let mut i = 0;
            while i < N {
                ret.array[N - 1 - i] = self.array[i].reverse_bits();
                i += 1;
            }
            ret
        }
        // TODO: Add big-endian support via #[cfg(target_endian = "big")]
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
}

c0nst::c0nst! {
    /// Const-callable `pow` body. Free-floating because the c0nst macro
    /// only accepts `[c0nst]` bounds on trait-impl headers and
    /// standalone `const fn` items, not on inherent `impl` blocks.
    pub(crate) c0nst fn pow_impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize>(
        v: FixedUInt<T, N, Nct>, exp: u32,
    ) -> FixedUInt<T, N, Nct> {
        if exp == 0 {
            return <FixedUInt<T, N, Nct> as const_num_traits::ConstOne>::ONE;
        }
        let mut result = <FixedUInt<T, N, Nct> as const_num_traits::ConstOne>::ONE;
        let mut base = v;
        let mut e = exp;
        while e > 0 {
            if (e & 1) == 1 {
                result = core::ops::Mul::mul(result, base);
            }
            e >>= 1;
            if e > 0 {
                base = core::ops::Mul::mul(base, base);
            }
        }
        result
    }
}

impl<T: ConstMachineWord + MachineWord, const N: usize> FixedUInt<T, N, Nct> {
    /// Inherent `pow`. `FixedUInt` does not implement external `PrimInt`
    /// (which supertrait-bundles `Num + NumCast + Saturating`), so this
    /// stays on the type itself. For const-callable use on nightly, call
    /// the free `pow_impl` function above directly.
    pub fn pow(self, exp: u32) -> Self {
        pow_impl(self, exp)
    }
}

#[cfg(feature = "num-traits")]
impl<T: MachineWord, const N: usize> num_traits::PrimInt for FixedUInt<T, N, Nct> {
    fn count_ones(self) -> u32 {
        self.array.iter().map(|&val| val.count_ones()).sum()
    }
    fn count_zeros(self) -> u32 {
        self.array.iter().map(|&val| val.count_zeros()).sum()
    }
    fn leading_zeros(self) -> u32 {
        const_leading_zeros(&self.array)
    }
    fn trailing_zeros(self) -> u32 {
        const_trailing_zeros(&self.array)
    }
    fn rotate_left(self, bits: u32) -> Self {
        let bit_size = Self::BIT_SIZE as u32;
        if bit_size == 0 {
            return self;
        }
        let shift = bits % bit_size;
        let a = self << shift;
        let b = self >> (bit_size - shift);
        a | b
    }
    fn rotate_right(self, bits: u32) -> Self {
        let bit_size = Self::BIT_SIZE as u32;
        if bit_size == 0 {
            return self;
        }
        let shift = bits % bit_size;
        let a = self >> shift;
        let b = self << (bit_size - shift);
        a | b
    }
    fn signed_shl(self, bits: u32) -> Self {
        <Self as num_traits::PrimInt>::unsigned_shl(self, bits)
    }
    fn signed_shr(self, bits: u32) -> Self {
        <Self as num_traits::PrimInt>::unsigned_shr(self, bits)
    }
    fn unsigned_shl(self, bits: u32) -> Self {
        self << bits
    }
    fn unsigned_shr(self, bits: u32) -> Self {
        self >> bits
    }
    fn swap_bytes(self) -> Self {
        let mut ret = Self::new();
        for index in 0..N {
            ret.array[index] = self.array[N - 1 - index].swap_bytes();
        }

        ret
    }
    // TODO: Add big-endian support via #[cfg(target_endian = "big")]
    fn from_be(source: Self) -> Self {
        <Self as num_traits::PrimInt>::swap_bytes(source)
    }
    fn from_le(source: Self) -> Self {
        source
    }
    fn to_be(self) -> Self {
        <Self as num_traits::PrimInt>::swap_bytes(self)
    }
    fn to_le(self) -> Self {
        self
    }
    fn pow(self, exp: u32) -> Self {
        if exp == 0 {
            return Self::one();
        }
        // Exponentiation by squaring: O(log exp) instead of O(exp)
        let mut result = Self::one();
        let mut base = self;
        let mut e = exp;
        while e > 0 {
            if (e & 1) == 1 {
                result *= base;
            }
            e >>= 1;
            if e > 0 {
                base *= base;
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::PrimBits;

    type U16 = FixedUInt<u8, 2, Nct>;

    // --- Empirical const-evaluability proofs for `PrimBits` ----------------
    //
    // Wraps each by-value `PrimBits` method in a `c0nst fn` so the
    // surrounding `c0nst::c0nst!` block forces it into const-callable
    // form on nightly. The `nightly_const_eval_prim_bits` test then binds
    // each wrapper's result to a `const` item, proving the trait method
    // actually evaluates at compile time.

    c0nst::c0nst! {
        pub c0nst fn const_count_ones<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> u32 {
            PrimBits::count_ones(v)
        }
        pub c0nst fn const_count_zeros<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> u32 {
            PrimBits::count_zeros(v)
        }
        pub c0nst fn const_leading_zeros<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> u32 {
            PrimBits::leading_zeros(v)
        }
        pub c0nst fn const_trailing_zeros<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> u32 {
            PrimBits::trailing_zeros(v)
        }
        pub c0nst fn const_swap_bytes<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            PrimBits::swap_bytes(v)
        }
        pub c0nst fn const_rotate_left<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            PrimBits::rotate_left(v, n)
        }
        pub c0nst fn const_rotate_right<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            PrimBits::rotate_right(v, n)
        }
        pub c0nst fn const_unsigned_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            PrimBits::unsigned_shl(v, n)
        }
        pub c0nst fn const_unsigned_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            PrimBits::unsigned_shr(v, n)
        }
        pub c0nst fn const_signed_shl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            PrimBits::signed_shl(v, n)
        }
        pub c0nst fn const_signed_shr<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>, n: u32) -> FixedUInt<T, N, P> {
            PrimBits::signed_shr(v, n)
        }
        pub c0nst fn const_reverse_bits<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            PrimBits::reverse_bits(v)
        }
        pub c0nst fn const_to_be<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            PrimBits::to_be(v)
        }
        pub c0nst fn const_to_le<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            PrimBits::to_le(v)
        }
        pub c0nst fn const_from_be<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            PrimBits::from_be(v)
        }
        pub c0nst fn const_from_le<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> FixedUInt<T, N, P> {
            PrimBits::from_le(v)
        }
    }

    #[test]
    fn nightly_const_eval_prim_bits() {
        // runtime smoke
        let v = U16::from(0b0010_1000u8);
        assert_eq!(const_count_ones(v), 2);
        assert_eq!(const_leading_zeros(v), 10);
        assert_eq!(const_trailing_zeros(v), 3);

        #[cfg(feature = "nightly")]
        {
            const V: U16 = FixedUInt::from_array([0x28, 0]);
            const V_FULL: U16 = FixedUInt::from_array([0xFF, 0xFF]);
            const V_ONE: U16 = FixedUInt::from_array([1, 0]);

            const C_ONES: u32 = const_count_ones(V);
            const C_ZEROS: u32 = const_count_zeros(V);
            const LZ: u32 = const_leading_zeros(V);
            const TZ: u32 = const_trailing_zeros(V);
            const SWAP: U16 = const_swap_bytes(V_ONE);
            const ROTL: U16 = const_rotate_left(V_ONE, 4);
            const ROTR: U16 = const_rotate_right(V_ONE, 4);
            const USHL: U16 = const_unsigned_shl(V_ONE, 4);
            const USHR: U16 = const_unsigned_shr(V_FULL, 4);
            const SSHL: U16 = const_signed_shl(V_ONE, 4);
            const SSHR: U16 = const_signed_shr(V_FULL, 4);
            const REV: U16 = const_reverse_bits(V_ONE);
            const TO_BE: U16 = const_to_be(V_ONE);
            const TO_LE: U16 = const_to_le(V_ONE);
            const FROM_BE: U16 = const_from_be(V_ONE);
            const FROM_LE: U16 = const_from_le(V_ONE);

            assert_eq!(C_ONES, 2);
            assert_eq!(C_ZEROS, 14);
            assert_eq!(LZ, 10);
            assert_eq!(TZ, 3);
            assert_eq!(SWAP.array, [0, 1]);
            assert_eq!(ROTL.array, [16, 0]);
            assert_eq!(ROTR.array, [0, 0x10]);
            assert_eq!(USHL.array, [16, 0]);
            assert_eq!(USHR.array, [0xFF, 0x0F]);
            assert_eq!(SSHL.array, [16, 0]);
            assert_eq!(SSHR.array, [0xFF, 0x0F]);
            assert_eq!(REV.array, [0, 0x80]);
            assert_eq!(TO_BE.array, [0, 1]);
            assert_eq!(TO_LE.array, [1, 0]);
            assert_eq!(FROM_BE.array, [0, 1]);
            assert_eq!(FROM_LE.array, [1, 0]);
        }
    }

    // --- Empirical const-eval proof for the standalone `pow_impl` ----------

    #[test]
    fn nightly_const_eval_pow() {
        // runtime smoke (works on stable + nightly)
        let v = U16::from(2u8);
        assert_eq!(super::pow_impl(v, 8), U16::from(256u16));
        assert_eq!(super::pow_impl(v, 0), U16::from(1u8));

        #[cfg(feature = "nightly")]
        {
            const TWO: U16 = FixedUInt::from_array([2, 0]);
            const THREE: U16 = FixedUInt::from_array([3, 0]);
            const TWO_TO_THE_EIGHT: U16 = super::pow_impl(TWO, 8);
            const THREE_TO_THE_FIVE: U16 = super::pow_impl(THREE, 5);
            const ZERO_EXP: U16 = super::pow_impl(TWO, 0);
            assert_eq!(TWO_TO_THE_EIGHT, FixedUInt::from_array([0, 1])); // 256
            assert_eq!(THREE_TO_THE_FIVE, FixedUInt::from_array([243, 0]));
            assert_eq!(ZERO_EXP, FixedUInt::from_array([1, 0]));
        }
    }
}
