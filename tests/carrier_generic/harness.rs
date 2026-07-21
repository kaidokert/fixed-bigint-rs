//! Behavior shared by every carrier — written once as a generic body and run
//! for both `FixedUInt` and `HeaplessBigInt`.
//!
//! Both carriers are pinned to the same 32-bit width so the overflow / carry /
//! wrap boundaries line up. Construction goes through the two traits both
//! carriers share — `From<u32>` then `WithPrecision::widen_to_precision(32)` —
//! because `From` alone is minimal-width on HeaplessBigInt and would otherwise
//! not match FixedUInt's fixed width.
//!
//! Tests that reach into a carrier's internals (limbs / len / CAP, personality,
//! the runtime-length width vocabulary) live in each carrier's own suite; this
//! file is only the surface both share.

pub(crate) use const_num_traits::{
    AbsDiff, BorrowingSub, Bounded, CarryingAdd, CarryingMul, CheckedAdd, CheckedDiv,
    CheckedEuclid, CheckedMul, CheckedPow, CheckedRem, CheckedShl, CheckedShr, CheckedSub,
    DepositBits, DivCeil, Euclid, ExtractBits, FunnelShl, FunnelShr, HighestOne, Ilog, Ilog2,
    Ilog10, IsPowerOfTwo, IsolateHighestOne, IsolateLowestOne, Isqrt, LowestOne, Midpoint,
    MultipleOf, Nct, NextMultipleOf, NextPowerOfTwo, One, OverflowingAdd, OverflowingMul,
    OverflowingShl, OverflowingShr, OverflowingSub, Parity, PrimBits, SaturatingAdd, SaturatingMul,
    SaturatingSub, ShlExact, ShrExact, StrictAdd, StrictDiv, StrictMul, StrictPow, StrictRem,
    StrictShl, StrictShr, StrictSub, UnboundedShl, UnboundedShr, WithPrecision, WrappingAdd,
    WrappingMul, WrappingShl, WrappingShr, WrappingSub, Zero,
};
pub(crate) use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
pub(crate) use fixed_bigint::{FixedUInt, HeaplessBigInt, MachineWord};

/// The 32-bit unsigned surface both carriers implement.
pub(crate) trait Carrier:
    Copy
    + core::fmt::Debug
    + PartialEq
    + PartialOrd
    + Zero
    + One
    + Bounded
    + Parity
    + From<u32>
    + WithPrecision
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitXor<Output = Self>
    + Shl<usize, Output = Self>
    + Shr<usize, Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + RemAssign
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + ShlAssign<usize>
    + ShrAssign<usize>
    + WrappingAdd<Output = Self>
    + WrappingSub<Output = Self>
    + WrappingMul<Output = Self>
    + OverflowingAdd<Output = Self>
    + OverflowingSub<Output = Self>
    + OverflowingMul<Output = Self>
    + CheckedAdd<Output = Self>
    + CheckedSub<Output = Self>
    + CheckedMul<Output = Self>
    + CheckedDiv<Output = Self>
    + CheckedRem<Output = Self>
    + SaturatingAdd<Output = Self>
    + SaturatingSub<Output = Self>
    + SaturatingMul<Output = Self>
    + CarryingMul<Unsigned = Self, Output = Self>
    + Not<Output = Self>
    + PrimBits
    + CheckedPow<Output = Self>
    + StrictPow<Output = Self>
    + StrictAdd<Output = Self>
    + StrictSub<Output = Self>
    + StrictMul<Output = Self>
    + StrictDiv<Output = Self>
    + StrictRem<Output = Self>
    + StrictShl<Output = Self>
    + StrictShr<Output = Self>
    + CarryingAdd<Output = Self>
    + BorrowingSub<Output = Self>
    + DivCeil<Output = Self>
    + Euclid<Output = Self>
    + CheckedEuclid
    + AbsDiff<Output = Self>
    + Midpoint<Output = Self>
    + IsPowerOfTwo
    + NextPowerOfTwo<Output = Self>
    + MultipleOf
    + NextMultipleOf<Output = Self>
    + Isqrt<Output = Self>
    + Ilog2
    + Ilog10
    + Ilog
    + HighestOne
    + LowestOne
    + IsolateHighestOne<Output = Self>
    + IsolateLowestOne<Output = Self>
    + core::iter::Sum
    + core::iter::Product
    + OverflowingShl<Output = Self>
    + OverflowingShr<Output = Self>
    + WrappingShl<Output = Self>
    + WrappingShr<Output = Self>
    + CheckedShl<Output = Self>
    + CheckedShr<Output = Self>
    + UnboundedShl<Output = Self>
    + UnboundedShr<Output = Self>
    + ShlExact<Output = Self>
    + ShrExact<Output = Self>
    + FunnelShl<Output = Self>
    + FunnelShr<Output = Self>
    + DepositBits<Output = Self>
    + ExtractBits<Output = Self>
{
    /// Build `v` pinned to the carrier's full 32-bit width. `From<u32>`
    /// alone is minimal-width on HeaplessBigInt (100 → one limb), so
    /// `widen_to_precision` pins it to 32 bits — an identity on FixedUInt,
    /// a grow on HeaplessBigInt — so the overflow boundaries line up.
    fn from_u32(v: u32) -> Self {
        <Self as From<u32>>::from(v).widen_to_precision(32)
    }
}

impl<
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + core::fmt::Debug + Parity,
    const N: usize,
> Carrier for FixedUInt<T, N, Nct>
{
}
impl<
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + core::fmt::Debug + Parity,
    const CAP: usize,
> Carrier for HeaplessBigInt<T, CAP, Nct>
{
}

/// Run a generic body for both carriers across three backings of the same
/// 32-bit width.
macro_rules! for_both_carriers {
    ($body:ident) => {{
        $body::<FixedUInt<u8, 4, Nct>>();
        $body::<HeaplessBigInt<u8, 4, Nct>>();
        $body::<FixedUInt<u16, 2, Nct>>();
        $body::<HeaplessBigInt<u16, 2, Nct>>();
        $body::<FixedUInt<u32, 1, Nct>>();
        $body::<HeaplessBigInt<u32, 1, Nct>>();
    }};
}

pub(crate) const MAX32: u32 = u32::MAX;

pub(crate) use for_both_carriers;
