//! `num_traits` bridge for `HeaplessBigInt` (feature = "num-traits").
//!
//! Thin forwards onto the const-num-traits identity/bounds impls plus
//! byte-based primitive extraction, mirroring `FixedUInt`'s bridge so a
//! `HeaplessBigInt` satisfies the classic `num_traits` bounds
//! (`Zero`/`One`/`Bounded`/`NumCast`/`ToPrimitive`/`FromPrimitive`). All
//! are personality-generic — no `Nct` gate, matching `FixedUInt`.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{Bounded, CarryingMul, ConstOne, ConstZero, Personality, Zero};

impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::Zero
    for HeaplessBigInt<T, CAP, P>
{
    fn zero() -> Self {
        <Self as ConstZero>::ZERO
    }

    fn is_zero(&self) -> bool {
        <Self as Zero>::is_zero(self)
    }
}

// `num_traits::One: Mul<Self>`, and heapless multiplication needs
// `CarryingMul` on the word (unlike `FixedUInt`, which widens via
// `DoubleWord`), so this impl carries the same bound its `Mul` does.
impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    num_traits::One for HeaplessBigInt<T, CAP, P>
{
    fn one() -> Self {
        <Self as ConstOne>::ONE
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::Bounded
    for HeaplessBigInt<T, CAP, P>
{
    fn min_value() -> Self {
        <Self as Bounded>::min_value()
    }

    fn max_value() -> Self {
        <Self as Bounded>::max_value()
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::ToPrimitive
    for HeaplessBigInt<T, CAP, P>
{
    fn to_i64(&self) -> Option<i64> {
        // Unsigned carrier: mirror `FixedUInt`, which never claims `i64`.
        None
    }

    fn to_u64(&self) -> Option<u64> {
        let word_size = core::mem::size_of::<T>();
        let len = self.len as usize;
        // Words that can reach the low 64 bits.
        let iter_limit = core::cmp::min(8 / word_size, len);
        // Anything set above bit 63 overflows a u64. Limbs beyond `len` are
        // zero by the zero-tail invariant, so scanning `iter_limit..len`
        // is enough.
        for i in iter_limit..len {
            if !super::is_zero(&self.limbs[i]) {
                return None;
            }
        }
        let mut ret: u64 = 0;
        for (i, word) in self.limbs.iter().take(iter_limit).enumerate() {
            let bytes = word.to_le_bytes();
            for (j, &byte) in bytes.as_ref().iter().enumerate() {
                let bit_shift = (i * word_size + j) * 8;
                if bit_shift < 64 {
                    ret |= (byte as u64) << bit_shift;
                }
            }
        }
        Some(ret)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::FromPrimitive
    for HeaplessBigInt<T, CAP, P>
{
    fn from_i64(_: i64) -> Option<Self> {
        None
    }

    fn from_u64(input: u64) -> Option<Self> {
        // Reject values the carrier can't hold. When `max` itself overflows
        // a u64 the carrier is >= 64 bits wide, so every u64 fits.
        if let Some(max) =
            num_traits::ToPrimitive::to_u64(&<Self as num_traits::Bounded>::max_value())
        {
            if input > max {
                return None;
            }
        }
        // Construct at natural width: trim trailing zero bytes so a small
        // value in a small-`CAP` carrier stays in bounds. (Unlike `From`,
        // which asserts on oversize — the trait contract here is to return
        // `None`, never panic, and the size check above already did that.)
        let bytes = input.to_le_bytes();
        let mut sig = bytes.len();
        while sig > 0 && bytes[sig - 1] == 0 {
            sig -= 1;
        }
        Some(Self::from_le_bytes(&bytes[..sig]))
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> num_traits::NumCast
    for HeaplessBigInt<T, CAP, P>
{
    fn from<X: num_traits::ToPrimitive>(arg: X) -> Option<Self> {
        <Self as num_traits::FromPrimitive>::from_u64(arg.to_u64()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Alias so the assertions exercise the *num_traits* bridge, not the
    // `const_num_traits::Bounded` pulled in by `super::*`.
    use num_traits::{Bounded as NumBounded, FromPrimitive, NumCast, One, ToPrimitive, Zero};

    type H8x4 = HeaplessBigInt<u8, 4>; // 32-bit carrier
    type H32x8 = HeaplessBigInt<u32, 8>; // 256-bit carrier

    #[test]
    fn zero_one_bounded() {
        assert!(<H8x4 as Zero>::zero().is_zero());
        assert!(!<H8x4 as One>::one().is_zero());
        // max is capacity-wide (all CAP limbs saturated).
        let max = <H8x4 as NumBounded>::max_value();
        assert_eq!(max.to_u64(), Some(0xFFFF_FFFF));
        assert!(<H8x4 as NumBounded>::min_value().is_zero());
    }

    #[test]
    fn to_u64_roundtrips_and_overflows() {
        // Fits.
        assert_eq!(
            H32x8::from_u64(0x1234_5678_9ABC).unwrap().to_u64(),
            Some(0x1234_5678_9ABC)
        );
        // 32-bit carrier can't hold a value above u32::MAX → to_u64 None path
        // is only reachable when higher limbs are set; here the value is built
        // from_u64 so overflow surfaces at construction instead.
        assert_eq!(H8x4::from_u64(0x1_0000_0000), None); // > u32::MAX
        assert_eq!(
            H8x4::from_u64(0xFFFF_FFFF).unwrap().to_u64(),
            Some(0xFFFF_FFFF)
        );
        assert_eq!(H8x4::from_u64(0).unwrap().to_u64(), Some(0));
    }

    #[test]
    fn numcast_between_widths() {
        let a: H32x8 = NumCast::from(255u32).unwrap();
        assert_eq!(a.to_u64(), Some(255));
        assert!(<H8x4 as NumCast>::from(0x1_0000_0000u64).is_none());
    }

    #[test]
    fn matches_fixeduint_reference() {
        // The bridge mirrors `FixedUInt`'s; at equal width the primitive
        // casts must agree value-for-value.
        type F32x8 = crate::FixedUInt<u32, 8>;
        for v in [0u64, 1, 0xFF, 0x1_0000, 0x1234_5678_9ABC_DEF0] {
            assert_eq!(
                H32x8::from_u64(v).unwrap().to_u64(),
                F32x8::from_u64(v).unwrap().to_u64(),
                "to_u64 mismatch for {v:#x}"
            );
        }
        // Overflow verdict agrees on a narrow (32-bit) carrier.
        assert!(H8x4::from_u64(0x1_0000_0000).is_none());
        assert!(crate::FixedUInt::<u8, 4>::from_u64(0x1_0000_0000).is_none());
    }

    #[test]
    fn from_u64_is_natural_width() {
        // A small value in a wide carrier constructs at its own width, not CAP.
        use const_num_traits::BitsPrecision;
        let small = H32x8::from_u64(1).unwrap();
        assert_eq!(small.bits_precision(), 32); // one u32 limb, not 8
    }
}
