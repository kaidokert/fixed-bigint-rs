//! Client-owned workload catalog (proof-of-concept slice).
//!
//! Each Ct operation is declared **once** as a carrier-generic function; the
//! backend adapters (asm-grep `extern "C"`, ctgrind taint, and — later — the
//! DWT paired hardware suite) all drive that single definition. The one thing
//! that genuinely differs between carriers — constructing the value from raw
//! words and reading it back — lives in [`FixtureCarrier`], not in every
//! fixture.
//!
//! This slice covers the `bin` shape via `sat_add` on both carriers, to prove
//! one op body feeds both the `A` (FixedUInt) and `HA` (Heapless) fixtures.
//! Remaining shapes/ops are migrated on top of this.

use const_num_traits::{
    AbsDiff, Ct, IsPowerOfTwo, Midpoint, NextPowerOfTwo, One, OverflowingAdd, OverflowingMul,
    OverflowingSub, PrimBits, SaturatingAdd, SaturatingMul, SaturatingSub, UnboundedShl,
    UnboundedShr, WrappingAdd, WrappingMul, WrappingSub, Zero,
};
use core::ops::{BitAnd, BitOr, BitXor, Not, Shl, ShlAssign, Shr, ShrAssign};
use fixed_bigint::{FixedUInt, HeaplessBigInt, MachineWord};
use subtle::{ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

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

/// `bin`-shape adapter: `(a, b) -> out`. Generates the `extern "C"` fixture
/// (and, under the `ctgrind` feature, its taint registration) for one
/// op × carrier × width by constructing the carrier through [`FixtureCarrier`],
/// calling the shared catalog op, and reading the result back. The op and its
/// input values are single-sourced; only the carrier + width vary here.
#[macro_export]
macro_rules! emit_wl_bin {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_bin!($sym, $T, $N, |aw, bw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            let b = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(bw);
            <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::to_words(&$op(a, b))
        });
    };
}

/// `un` shape: `(a) -> out`.
#[macro_export]
macro_rules! emit_wl_un {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_un!($sym, $T, $N, |aw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::to_words(&$op(a))
        });
    };
}

/// `count` shape: `(a) -> u32`.
#[macro_export]
macro_rules! emit_wl_count {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_count!($sym, $T, $N, |aw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            $op(a)
        });
    };
}

/// `pred` shape: `(a) -> u8`.
#[macro_export]
macro_rules! emit_wl_pred {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_pred!($sym, $T, $N, |aw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            $op(a)
        });
    };
}

/// `pred2` shape: `(a, b) -> u8`.
#[macro_export]
macro_rules! emit_wl_pred2 {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_pred2!($sym, $T, $N, |aw, bw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            let b = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(bw);
            $op(a, b)
        });
    };
}

/// `shift` shape: `(a, amount) -> out`. `$NT` is the amount type (`usize`/`u32`).
#[macro_export]
macro_rules! emit_wl_shift {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal, $NT:ty) => {
        $crate::ct_fix_shift!($sym, $T, $N, $NT, |aw, n| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::to_words(&$op(a, n))
        });
    };
}
