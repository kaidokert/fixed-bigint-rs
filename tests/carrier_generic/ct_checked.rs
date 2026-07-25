//! Cross-carrier parity for the constant-time checked traits — `CtCheckedAdd`,
//! `CtCheckedSub`, `CtCheckedMul`, and `CtNonZero`.
//!
//! The shared `Carrier` harness is `Nct`-only, so it can't reach these
//! (they're `Ct`-personality). This file carries a parallel `CtCarrier`
//! surface and runs each body for both `FixedUInt<_,_,Ct>` and
//! `HeaplessBigInt<_,_,Ct>` at the shared 32-bit width. Both carriers already
//! have per-carrier unit tests; what was missing is a check that the two impls
//! agree on the same inputs — asserting each against the same expected
//! `(value, validity)` pins them equal, extending the `HeaplessBigInt ≡
//! FixedUInt` invariant to the masked-return CT surface.

use crate::harness::{Bounded, CarryingMul, FixedUInt, HeaplessBigInt, MachineWord, Parity};
use const_num_traits::ops::ct::{CtCheckedAdd, CtCheckedMul, CtCheckedSub};
use const_num_traits::{Ct, CtNonZero, HasNonZero, One, WithPrecision, Zero};

const MAX32: u32 = u32::MAX;

/// The `Ct` checked-arithmetic surface both carriers implement, plus the
/// width-pinning constructor. Mirrors `harness::Carrier` but for the Ct traits.
pub(crate) trait CtCarrier:
    Copy
    + core::fmt::Debug
    + PartialEq
    + Zero
    + One
    + Bounded
    + From<u32>
    + WithPrecision
    + CtCheckedAdd
    + CtCheckedSub
    + CtCheckedMul
    + HasNonZero
    + CtNonZero
{
    /// Pin `v` to the carrier's full 32-bit width, so the overflow boundaries
    /// line up across carriers (identity on `FixedUInt`, a grow on heapless).
    fn from_u32_ct(v: u32) -> Self {
        <Self as From<u32>>::from(v).widen_to_precision(32)
    }
}

impl<T, const N: usize> CtCarrier for FixedUInt<T, N, Ct> where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + subtle::ConstantTimeEq + Parity
{
}
impl<T, const CAP: usize> CtCarrier for HeaplessBigInt<T, CAP, Ct> where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + subtle::ConstantTimeEq + Parity
{
}

macro_rules! for_both_ct_carriers {
    ($body:ident) => {{
        $body::<FixedUInt<u8, 4, Ct>>();
        $body::<HeaplessBigInt<u8, 4, Ct>>();
        $body::<FixedUInt<u16, 2, Ct>>();
        $body::<HeaplessBigInt<u16, 2, Ct>>();
        $body::<FixedUInt<u32, 1, Ct>>();
        $body::<HeaplessBigInt<u32, 1, Ct>>();
    }};
}

#[test]
fn ct_checked_add_parity() {
    fn body<C: CtCarrier>() {
        let a = C::from_u32_ct(250);
        let b = C::from_u32_ct(5);
        assert_eq!(
            Option::<C>::from(a.ct_checked_add(&b)),
            Some(C::from_u32_ct(255))
        );
        // Overflow at the shared 32-bit width masks to None on both carriers.
        let max = C::from_u32_ct(MAX32);
        let one = C::from_u32_ct(1);
        assert_eq!(Option::<C>::from(max.ct_checked_add(&one)), None);
    }
    for_both_ct_carriers!(body);
}

#[test]
fn ct_checked_sub_parity() {
    fn body<C: CtCarrier>() {
        let a = C::from_u32_ct(500);
        let b = C::from_u32_ct(200);
        assert_eq!(
            Option::<C>::from(a.ct_checked_sub(&b)),
            Some(C::from_u32_ct(300))
        );
        // Underflow masks to None.
        let one = C::from_u32_ct(1);
        let two = C::from_u32_ct(2);
        assert_eq!(Option::<C>::from(one.ct_checked_sub(&two)), None);
    }
    for_both_ct_carriers!(body);
}

#[test]
fn ct_checked_mul_parity() {
    fn body<C: CtCarrier>() {
        let a = C::from_u32_ct(1000);
        let b = C::from_u32_ct(1000);
        assert_eq!(
            Option::<C>::from(a.ct_checked_mul(&b)),
            Some(C::from_u32_ct(1_000_000))
        );
        // 100_000^2 = 10^10 overflows 32 bits → None on both carriers.
        let big = C::from_u32_ct(100_000);
        assert_eq!(Option::<C>::from(big.ct_checked_mul(&big)), None);
    }
    for_both_ct_carriers!(body);
}

#[test]
fn into_nonzero_ct_parity() {
    fn body<C: CtCarrier>() {
        // Non-zero → the masked `CtOption` is Some; zero → None. This pins the
        // validity flag across carriers (value recovery via the inherent
        // `NonZero::get()` is covered per-carrier).
        assert!(bool::from(C::from_u32_ct(7).into_nonzero_ct().is_some()));
        assert!(bool::from(C::from_u32_ct(0).into_nonzero_ct().is_none()));
    }
    for_both_ct_carriers!(body);
}
