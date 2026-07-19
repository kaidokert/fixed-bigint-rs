//! `HasNonZero` / `DivNonZero` / `CtNonZero` for `HeaplessBigInt`, plus the
//! [`NonZeroHeaplessBigInt`] proof-type they hand out.
//!
//! Mirrors `FixedUInt`'s `has_nonzero_impl.rs`: `into_nonzero` returns a
//! branchful `Option` (fine for public moduli); secret-derived proofs go
//! through `CtNonZero::into_nonzero_ct`, a masked-return `CtOption`. None of
//! this needs `const_ct_select` — `into_nonzero_ct` masks with `ct_is_zero`
//! and `subtle::CtOption`, both of which heapless already carries.

// `let _ = <Self as AssertNonzeroCarrier>::CHECK;` in `Default::default()`
// forces monomorphization-time evaluation of the `CAP > 0` assertion (same
// idiom as `AssertCapFits` in this module).
#![allow(clippy::let_unit_value)]

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, Ct, DivNonZero, HasNonZero, Nct, One, Personality, Zero};

/// Non-zero [`HeaplessBigInt`]. Constructed via [`HasNonZero::into_nonzero`].
///
/// `#[repr(transparent)]` over the inner value: identical layout, so the
/// wrapper round-trips at the same ABI. Always `Copy` (matches
/// `HasNonZero::NonZero: Copy`).
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NonZeroHeaplessBigInt<T, const CAP: usize, P: Personality>(HeaplessBigInt<T, CAP, P>)
where
    T: MachineWord;

// Manual `Debug` (not derive): the Nct arm needs `T: Debug`, the Ct arm is
// opaque, matching `HeaplessBigInt`'s own personality-split `Debug`.
impl<T: MachineWord + core::fmt::Debug, const CAP: usize> core::fmt::Debug
    for NonZeroHeaplessBigInt<T, CAP, Nct>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NonZero({:?})", self.0)
    }
}

impl<T: MachineWord, const CAP: usize> core::fmt::Debug for NonZeroHeaplessBigInt<T, CAP, Ct> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NonZero({:?})", self.0)
    }
}

impl<T, const CAP: usize, P: Personality> NonZeroHeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    /// Recover the underlying [`HeaplessBigInt`].
    #[inline]
    pub fn get(self) -> HeaplessBigInt<T, CAP, P> {
        self.0
    }
}

// Type-level `CAP > 0` guard — a `CAP == 0` carrier can't store the `1` that
// `Default` produces. Associated-const form so it fires at monomorphization.
trait AssertNonzeroCarrier {
    const CHECK: ();
}
impl<T: MachineWord, const CAP: usize, P: Personality> AssertNonzeroCarrier
    for NonZeroHeaplessBigInt<T, CAP, P>
{
    const CHECK: () = assert!(
        CAP > 0,
        "NonZeroHeaplessBigInt::default() requires CAP > 0 (a CAP=0 carrier can only hold zero)"
    );
}

// `Default` is the non-zero value 1, the same convention as
// `core::num::NonZero`, carried at **full capacity** (`len == CAP`) — the
// CAP-width analog of FixedUInt's N-width `NonZeroFixedUInt::default()`. Built
// value-based via `One` (not the source-width `From<u8>`) then widened. Needed
// by `subtle::CtOption` combinators whose bound is `T: Default +
// ConditionallySelectable`; `conditional_select` handles any len safely
// (output width is `max(len)`, choice-independent), but matching FixedUInt's
// full width keeps the two carriers' Default shapes aligned.
impl<T, const CAP: usize, P: Personality> Default for NonZeroHeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn default() -> Self {
        let _ = <Self as AssertNonzeroCarrier>::CHECK;
        NonZeroHeaplessBigInt(<HeaplessBigInt<T, CAP, P> as One>::one().widened(CAP as u16))
    }
}

// Ct-only, mirroring `HeaplessBigInt`'s own `ConditionallySelectable`. Both
// arms carry the "value != 0" invariant, so the selected value is non-zero
// regardless of which is taken.
impl<T, const CAP: usize> subtle::ConditionallySelectable for NonZeroHeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        Self(
            <HeaplessBigInt<T, CAP, Ct> as subtle::ConditionallySelectable>::conditional_select(
                &a.0, &b.0, choice,
            ),
        )
    }
}

impl<T, const CAP: usize, P: Personality> HasNonZero for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type NonZero = NonZeroHeaplessBigInt<T, CAP, P>;

    /// `Option` is branchful at the call site — fine for public inputs; a
    /// secret-derived `self` should route through
    /// [`CtNonZero::into_nonzero_ct`](const_num_traits::CtNonZero) instead.
    #[inline]
    fn into_nonzero(self) -> Option<Self::NonZero> {
        if <Self as Zero>::is_zero(&self) {
            None
        } else {
            Some(NonZeroHeaplessBigInt(self))
        }
    }

    #[inline]
    fn nonzero_get(nz: Self::NonZero) -> Self {
        nz.0
    }
}

// `DivNonZero` is Nct-only because `Div`/`Rem` on `HeaplessBigInt` are
// (long division is value-dependent). The `NonZero` proof-type discharges the
// divide-by-zero check, so these never hit the `Div` panic path.
impl<T, const CAP: usize> DivNonZero for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;

    #[inline]
    fn div_nonzero(self, d: Self::NonZero) -> Self::Output {
        self / d.0
    }

    #[inline]
    fn rem_nonzero(self, d: Self::NonZero) -> Self::Output {
        self % d.0
    }
}

// `CtNonZero` — masked-return `into_nonzero`; the `Choice` mask is value-level
// and CT-uniform across personalities. No `const_ct_select` needed.
impl<T, const CAP: usize, P: Personality> const_num_traits::CtNonZero for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn into_nonzero_ct(self) -> subtle::CtOption<Self::NonZero> {
        use const_num_traits::ops::ct::CtIsZero;
        let zero = self.ct_is_zero();
        subtle::CtOption::new(NonZeroHeaplessBigInt(self), !zero)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::CtNonZero;

    type H = HeaplessBigInt<u8, 4, Nct>;
    type HCt = HeaplessBigInt<u8, 4, Ct>;

    #[test]
    fn into_nonzero_some_none() {
        assert!(H::from(5u32).into_nonzero().is_some());
        assert!(H::from(0u32).into_nonzero().is_none());
    }

    #[test]
    fn default_is_one_at_full_capacity() {
        // Value 1, carried at CAP (matching FixedUInt's full-width default).
        let d = <NonZeroHeaplessBigInt<u8, 4, Nct> as Default>::default();
        assert_eq!(d.get(), H::from(1u8));
        assert_eq!(d.get().len(), 4);
    }

    #[test]
    fn nonzero_round_trip() {
        let v = H::from(42u32);
        let nz = v.into_nonzero().unwrap();
        assert_eq!(<H as HasNonZero>::nonzero_get(nz), v);
        assert_eq!(nz.get(), v);
    }

    #[test]
    fn div_rem_nonzero_match_operators() {
        let a = H::from(100u32);
        let m = H::from(7u32);
        let nz = m.into_nonzero().unwrap();
        assert_eq!(<H as DivNonZero>::div_nonzero(a, nz), a / m);
        assert_eq!(<H as DivNonZero>::rem_nonzero(a, nz), a % m);
    }

    // `DivNonZero for HeaplessBigInt<_, _, Ct>` must NOT exist (Div is
    // Nct-only); the `HasNonZero` proof-type is still P-generic.
    static_assertions::assert_not_impl_any!(HeaplessBigInt<u8, 4, Ct>: DivNonZero);

    #[test]
    fn into_nonzero_ct_masks_zero() {
        let nz = H::from(5u32).into_nonzero_ct();
        assert!(bool::from(nz.is_some()));
        assert_eq!(nz.unwrap().get(), H::from(5u32));
        assert!(!bool::from(H::from(0u32).into_nonzero_ct().is_some()));

        // Ct carrier: masking works without revealing the zero-ness branchfully.
        let nz_ct = HCt::from(42u32);
        assert!(bool::from(nz_ct.into_nonzero_ct().is_some()));
        let z_ct = HCt::from(0u32);
        assert!(!bool::from(z_ct.into_nonzero_ct().is_some()));
    }
}
