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
    AbsDiff, Ct, Midpoint, OverflowingAdd, OverflowingMul, OverflowingSub, SaturatingAdd,
    SaturatingMul, SaturatingSub, WrappingAdd, WrappingMul, WrappingSub,
};
use core::ops::{BitAnd, BitOr, BitXor};
use fixed_bigint::{FixedUInt, HeaplessBigInt, MachineWord};

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
