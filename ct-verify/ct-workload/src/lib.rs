#![no_std]

//! Client-owned workload catalog.
//!
//! Each Ct operation is declared **once** as a carrier-generic function; the
//! backend adapters (asm-grep `extern "C"`, ctgrind taint, and — later — the
//! DWT paired hardware suite) all drive that single definition. The one thing
//! that genuinely differs between carriers — constructing the value from raw
//! words and reading it back — lives in [`FixtureCarrier`], not in every
//! fixture.
//!
//! Every operation present on **both** carriers (FixedUInt `A/B/C/CT` and
//! Heapless `HA/HB/HC/HCT`) routes through here: the `bin`/`un`/`count`/`pred`/
//! `pred2`/`shift`/`checked_bin` shapes via the `emit_wl_*` adapters, plus the
//! bespoke-ABI ops (carrying/borrowing, carrying_mul, cond_select, cios row
//! ops) whose custom fixtures call the shared op body directly.
//!
//! Ops that live on only one carrier stay in their fixture file — the catalog
//! removes cross-carrier duplication, and there is none to remove for
//! `forget_ct`, `asym_*`, or the FixedUInt-only inherent `ct_checked_shl/shr/
//! pow/next_power_of_two`.

use const_num_traits::ops::ct::{
    CtCheckedAdd, CtCheckedMul, CtCheckedSub, CtIsPowerOfTwo, CtIsZero, CtParity,
};
use const_num_traits::{
    AbsDiff, BorrowingSub, CarryingAdd, CarryingMul, Ct, Ilog10, IsPowerOfTwo, Midpoint,
    NextPowerOfTwo, One, OverflowingAdd, OverflowingMul, OverflowingSub, PrimBits, SaturatingAdd,
    SaturatingMul, SaturatingSub, UnboundedShl, UnboundedShr, WrappingAdd, WrappingMul,
    WrappingSub, Zero,
};
use core::ops::{BitAnd, BitOr, BitXor, Div, Not, Shl, ShlAssign, Shr, ShrAssign};
use fixed_bigint::{FixedUInt, HeaplessBigInt, MachineWord};
use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

/// Build a Ct carrier from an `[T; N]` word array and read it back. This is the
/// only per-carrier plumbing a workload needs; everything else is generic.
pub trait FixtureCarrier<T: Copy, const N: usize>: Sized {
    fn from_words(words: [T; N]) -> Self;
    fn to_words(&self) -> [T; N];
}

impl<T: MachineWord, const N: usize> FixtureCarrier<T, N> for FixedUInt<T, N, Ct> {
    #[inline(always)]
    fn from_words(words: [T; N]) -> Self {
        FixedUInt::from(words)
    }
    #[inline(always)]
    fn to_words(&self) -> [T; N] {
        *self.words()
    }
}

impl<T: MachineWord, const N: usize> FixtureCarrier<T, N> for HeaplessBigInt<T, N, Ct> {
    #[inline(always)]
    fn from_words(words: [T; N]) -> Self {
        // Full-width `len == N` so it behaves bit-for-bit like `FixedUInt<T, N>`.
        HeaplessBigInt::from_limbs(words, N as u16)
    }
    #[inline(always)]
    fn to_words(&self) -> [T; N] {
        *self.all_limbs()
    }
}

// ── Workload ops (one definition per operation, carrier-generic) ──
// These are also the exact entry points the DWT hardware suite calls, so the
// workload body exists in exactly one place.

/// `bin` shape: `(C, C) -> C`. One definition each, shared by both carriers.
#[inline(always)]
pub fn sat_add<C: SaturatingAdd<Output = C>>(a: C, b: C) -> C {
    SaturatingAdd::saturating_add(a, b)
}
#[inline(always)]
pub fn sat_sub<C: SaturatingSub<Output = C>>(a: C, b: C) -> C {
    SaturatingSub::saturating_sub(a, b)
}
#[inline(always)]
pub fn sat_mul<C: SaturatingMul<Output = C>>(a: C, b: C) -> C {
    SaturatingMul::saturating_mul(a, b)
}
#[inline(always)]
pub fn abs_diff<C: AbsDiff<Output = C>>(a: C, b: C) -> C {
    AbsDiff::abs_diff(a, b)
}
#[inline(always)]
pub fn midpoint<C: Midpoint<Output = C>>(a: C, b: C) -> C {
    Midpoint::midpoint(a, b)
}
#[inline(always)]
pub fn bitand<C: BitAnd<Output = C>>(a: C, b: C) -> C {
    BitAnd::bitand(a, b)
}
#[inline(always)]
pub fn bitor<C: BitOr<Output = C>>(a: C, b: C) -> C {
    BitOr::bitor(a, b)
}
#[inline(always)]
pub fn bitxor<C: BitXor<Output = C>>(a: C, b: C) -> C {
    BitXor::bitxor(a, b)
}
#[inline(always)]
pub fn wrapping_add<C: WrappingAdd<Output = C>>(a: C, b: C) -> C {
    WrappingAdd::wrapping_add(a, b)
}
#[inline(always)]
pub fn wrapping_sub<C: WrappingSub<Output = C>>(a: C, b: C) -> C {
    WrappingSub::wrapping_sub(a, b)
}
#[inline(always)]
pub fn wrapping_mul<C: WrappingMul<Output = C>>(a: C, b: C) -> C {
    WrappingMul::wrapping_mul(a, b)
}
/// Overflowing forms discard the flag — the fixture checks the value path's
/// branch-freeness, and the ABI stays `bin`.
#[inline(always)]
pub fn overflowing_add<C: OverflowingAdd<Output = C>>(a: C, b: C) -> C {
    OverflowingAdd::overflowing_add(a, b).0
}
#[inline(always)]
pub fn overflowing_sub<C: OverflowingSub<Output = C>>(a: C, b: C) -> C {
    OverflowingSub::overflowing_sub(a, b).0
}
#[inline(always)]
pub fn overflowing_mul<C: OverflowingMul<Output = C>>(a: C, b: C) -> C {
    OverflowingMul::overflowing_mul(a, b).0
}

/// `un` shape: `(C) -> C`.
#[inline(always)]
pub fn not<C: Not<Output = C>>(a: C) -> C {
    Not::not(a)
}
#[inline(always)]
pub fn swap_bytes<C: PrimBits>(a: C) -> C {
    PrimBits::swap_bytes(a)
}
#[inline(always)]
pub fn reverse_bits<C: PrimBits>(a: C) -> C {
    PrimBits::reverse_bits(a)
}
#[inline(always)]
pub fn next_pow2<C: NextPowerOfTwo<Output = C>>(a: C) -> C {
    NextPowerOfTwo::next_power_of_two(a)
}
#[inline(always)]
pub fn wrapping_next_pow2<C: NextPowerOfTwo<Output = C>>(a: C) -> C {
    NextPowerOfTwo::wrapping_next_power_of_two(a)
}

/// `count` shape: `(C) -> u32`.
#[inline(always)]
pub fn count_ones<C: PrimBits>(a: C) -> u32 {
    PrimBits::count_ones(a)
}
#[inline(always)]
pub fn leading_zeros<C: PrimBits>(a: C) -> u32 {
    PrimBits::leading_zeros(a)
}
#[inline(always)]
pub fn trailing_zeros<C: PrimBits>(a: C) -> u32 {
    PrimBits::trailing_zeros(a)
}

/// `pred` shape: `(C) -> u8`.
#[inline(always)]
pub fn is_zero<C: Zero>(a: C) -> u8 {
    Zero::is_zero(&a) as u8
}
#[inline(always)]
pub fn is_one<C: One>(a: C) -> u8 {
    One::is_one(&a) as u8
}
#[inline(always)]
pub fn is_pow2<C: IsPowerOfTwo>(a: C) -> u8 {
    IsPowerOfTwo::is_power_of_two(a) as u8
}

/// `pred2` shape: `(C, C) -> u8`.
#[inline(always)]
pub fn cmp<C: Ord>(a: C, b: C) -> u8 {
    (a.cmp(&b) as i8) as u8
}
#[inline(always)]
pub fn eq<C: PartialEq>(a: C, b: C) -> u8 {
    (a == b) as u8
}
#[inline(always)]
pub fn ct_eq<C: ConstantTimeEq>(a: C, b: C) -> u8 {
    a.ct_eq(&b).unwrap_u8()
}
#[inline(always)]
pub fn ct_gt<C: ConstantTimeGreater>(a: C, b: C) -> u8 {
    a.ct_gt(&b).unwrap_u8()
}
#[inline(always)]
pub fn ct_lt<C: ConstantTimeLess>(a: C, b: C) -> u8 {
    a.ct_lt(&b).unwrap_u8()
}

/// `shift` shape: `(C, amount) -> C`. Assign forms mutate then return; the
/// unbounded forms take a `u32` amount.
#[inline(always)]
pub fn shl_usize<C: Shl<usize, Output = C>>(a: C, n: usize) -> C {
    a << n
}
#[inline(always)]
pub fn shr_usize<C: Shr<usize, Output = C>>(a: C, n: usize) -> C {
    a >> n
}
#[inline(always)]
pub fn shl_assign<C: ShlAssign<usize>>(mut a: C, n: usize) -> C {
    a <<= n;
    a
}
#[inline(always)]
pub fn shr_assign<C: ShrAssign<usize>>(mut a: C, n: usize) -> C {
    a >>= n;
    a
}
#[inline(always)]
pub fn unbounded_shl<C: UnboundedShl<Output = C>>(a: C, n: u32) -> C {
    UnboundedShl::unbounded_shl(a, n)
}
#[inline(always)]
pub fn unbounded_shr<C: UnboundedShr<Output = C>>(a: C, n: u32) -> C {
    UnboundedShr::unbounded_shr(a, n)
}

/// `pred` shape via the masked-`Choice` `Ct*` traits.
#[inline(always)]
pub fn ct_is_odd<C: CtParity>(a: C) -> u8 {
    a.ct_is_odd().unwrap_u8()
}
#[inline(always)]
pub fn ct_is_zero<C: CtIsZero>(a: C) -> u8 {
    a.ct_is_zero().unwrap_u8()
}
#[inline(always)]
pub fn ct_is_pow2<C: CtIsPowerOfTwo>(a: C) -> u8 {
    a.ct_is_power_of_two().unwrap_u8()
}

/// `checked_bin` shape: returns the masked `CtOption`; the adapter splits it
/// into (value, validity) with a zero fallback.
#[inline(always)]
pub fn ct_checked_add<C: CtCheckedAdd>(a: C, b: C) -> subtle::CtOption<C> {
    a.ct_checked_add(&b)
}
#[inline(always)]
pub fn ct_checked_sub<C: CtCheckedSub>(a: C, b: C) -> subtle::CtOption<C> {
    a.ct_checked_sub(&b)
}
#[inline(always)]
pub fn ct_checked_mul<C: CtCheckedMul>(a: C, b: C) -> subtle::CtOption<C> {
    a.ct_checked_mul(&b)
}

// ── Bespoke-ABI ops: op body single-sourced here; the fixtures keep their
// custom `extern "C"` wrappers but call these so both carriers share the body.

/// `(a, b, carry) -> (sum, carry_out)`.
#[inline(always)]
pub fn carrying_add<C: CarryingAdd<Output = C>>(a: C, b: C, carry: bool) -> (C, bool) {
    CarryingAdd::carrying_add(a, b, carry)
}
/// `(a, b, borrow) -> (diff, borrow_out)`.
#[inline(always)]
pub fn borrowing_sub<C: BorrowingSub<Output = C>>(a: C, b: C, borrow: bool) -> (C, bool) {
    BorrowingSub::borrowing_sub(a, b, borrow)
}
/// Widening `(a, b, carry) -> (lo, hi)`.
#[inline(always)]
pub fn carrying_mul<C: CarryingMul<Unsigned = C, Output = C>>(a: C, b: C, carry: C) -> (C, C) {
    CarryingMul::carrying_mul(a, b, carry)
}
/// Branchless select of `a`/`b` on `choice`'s low bit.
#[inline(always)]
pub fn cond_select<C: ConditionallySelectable>(a: C, b: C, choice: u8) -> C {
    C::conditional_select(&a, &b, Choice::from(choice))
}

/// CIOS Montgomery row ops. `acc` is taken by value and returned (the fixture
/// then writes it out) alongside the carry word, so the op stays a plain
/// value→value function callable from any backend.
#[cfg(feature = "cios")]
#[inline(always)]
pub fn cios_mul_acc_row<C: modmath_cios::CiosRowOps>(
    scalar: C::Word,
    mult: C,
    mut acc: C,
    carry: C::Word,
) -> (C, C::Word) {
    let c = <C as modmath_cios::CiosRowOps>::mul_acc_row(scalar, &mult, &mut acc, carry);
    (acc, c)
}
#[cfg(feature = "cios")]
#[inline(always)]
pub fn cios_mul_acc_shift_row<C: modmath_cios::CiosRowOps>(
    scalar: C::Word,
    mult: C,
    mut acc: C,
    acc_hi: C::Word,
) -> (C, C::Word) {
    let c = <C as modmath_cios::CiosRowOps>::mul_acc_shift_row(scalar, &mult, &mut acc, acc_hi);
    (acc, c)
}

// ── Ops used only by the DWT hardware suite (single-carrier, not fixtured on
// both carriers, but the workload body still lives here so the rig calls the
// same catalog as the emulated backends). ──

/// Scalar checked shift/pow — inherent methods on `FixedUInt` (Heapless has no
/// equivalent), wrapped in a trait so a workload can call them generically.
pub trait CtScalarChecked: Sized {
    fn wl_ct_checked_shl(self, n: u32) -> subtle::CtOption<Self>;
    fn wl_ct_checked_pow(self, exp: u32) -> subtle::CtOption<Self>;
}
impl<T: MachineWord, const N: usize> CtScalarChecked for FixedUInt<T, N, Ct> {
    #[inline(always)]
    fn wl_ct_checked_shl(self, n: u32) -> subtle::CtOption<Self> {
        self.ct_checked_shl(n)
    }
    #[inline(always)]
    fn wl_ct_checked_pow(self, exp: u32) -> subtle::CtOption<Self> {
        self.ct_checked_pow(exp)
    }
}
#[inline(always)]
pub fn ct_checked_shl<C: CtScalarChecked>(a: C, n: u32) -> subtle::CtOption<C> {
    a.wl_ct_checked_shl(n)
}
#[inline(always)]
pub fn ct_checked_pow<C: CtScalarChecked>(a: C, exp: u32) -> subtle::CtOption<C> {
    a.wl_ct_checked_pow(exp)
}

/// Negative-control ops (variable-time on `Nct` carriers): plain division and
/// base-10 log. Generic over the op trait, so the rig drives an `Nct` carrier.
#[inline(always)]
pub fn nct_div<C: Div<Output = C>>(a: C, b: C) -> C {
    a / b
}
#[inline(always)]
pub fn nct_ilog10<C: Ilog10>(a: C) -> u32 {
    Ilog10::ilog10(a)
}
