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

use const_num_traits::{Ct, SaturatingAdd};
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

/// `a.saturating_add(b)` at the operand width.
#[inline(always)]
pub fn sat_add<C: SaturatingAdd<Output = C>>(a: C, b: C) -> C {
    SaturatingAdd::saturating_add(a, b)
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
