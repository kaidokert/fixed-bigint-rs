// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! `HasNonZero` + `DivNonZero` carrier impls for `FixedUInt`.
//!
//! `HasNonZero::into_nonzero` returns `Option`, which is branchful at
//! the call site. Fine for public moduli; secret-derived proofs go
//! through `CtNonZero::into_nonzero_ct` (a masked-return `CtOption`)
//! implemented lower in this file.

// `let _ = <T as AssertNonzeroCarrier>::CHECK;` in `Default::default()`
// binds a unit-typed associated const to force monomorphization-time
// evaluation of the `N > 0` assertion. Same idiom as
// `byte_conversion_panic_free.rs`.
#![allow(clippy::let_unit_value)]

use super::{FixedUInt, MachineWord};
use crate::machineword::ConstMachineWord;
use const_num_traits::Zero;
use const_num_traits::{DivNonZero, HasNonZero, Nct, Personality};

/// Non-zero `FixedUInt`. Constructed via [`HasNonZero::into_nonzero`].
///
/// `#[repr(transparent)]` over `FixedUInt<T, N, P>` — the layout is
/// identical, so `NonZeroFixedUInt` can round-trip through FFI at the
/// same ABI as the inner. Always `Copy` (matches
/// `HasNonZero::NonZero: Copy`); the drop of the inner runs because
/// the field is owned, not because of the repr.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NonZeroFixedUInt<T, const N: usize, P: Personality>(FixedUInt<T, N, P>)
where
    T: MachineWord;

// Manual `Debug` (not `#[derive]`) — Nct needs `T: Debug`, Ct doesn't;
// a derive would add a uniform bound the Ct arm shouldn't require.
impl<T: MachineWord + core::fmt::Debug, const N: usize> core::fmt::Debug
    for NonZeroFixedUInt<T, N, const_num_traits::Nct>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NonZero({:?})", self.0)
    }
}

impl<T: MachineWord, const N: usize> core::fmt::Debug
    for NonZeroFixedUInt<T, N, const_num_traits::Ct>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Ct's `FixedUInt::Debug` doesn't reveal contents (CT hygiene);
        // we propagate that.
        write!(f, "NonZero({:?})", self.0)
    }
}

impl<T, const N: usize, P: Personality> NonZeroFixedUInt<T, N, P>
where
    T: MachineWord,
{
    /// Recover the underlying `FixedUInt`.
    #[inline]
    pub fn get(self) -> FixedUInt<T, N, P> {
        self.0
    }
}

// Type-level compile-time assertion `N > 0`. `const { assert!(N > 0) }`
// inside a fn body is rejected on nightly with `generic_const_exprs` as
// "overly complex generic constant" (blocks aren't supported there).
// Moving the assertion to an associated const on a trait impl sidesteps
// that — same pattern as `AssertBufferFits` in
// `byte_conversion_panic_free.rs`.
trait AssertNonzeroCarrier {
    const CHECK: ();
}
impl<T: MachineWord, const N: usize, P: Personality> AssertNonzeroCarrier
    for NonZeroFixedUInt<T, N, P>
{
    const CHECK: () = assert!(
        N > 0,
        "NonZeroFixedUInt::default() requires N > 0 (an N=0 carrier can only represent zero)"
    );
}

// `Default` returns the smallest non-zero value (1). Convention: the
// "default non-zero" is the multiplicative identity, the same shape
// `core::num::NonZero` uses (`NonZero::<u32>::new(1).unwrap()`). Needed
// by `subtle::CtOption::map` whose bound is `T: Default +
// ConditionallySelectable` on the input value type.
impl<T, const N: usize, P: Personality> Default for NonZeroFixedUInt<T, N, P>
where
    T: MachineWord,
{
    fn default() -> Self {
        // Fires at monomorphization when N == 0.
        let _ = <Self as AssertNonzeroCarrier>::CHECK;
        // Under N > 0, `FixedUInt::from(1u8)` writes 1 into the low limb
        // so the value is non-zero.
        NonZeroFixedUInt(FixedUInt::from(1u8))
    }
}

// Ct-only (mirrors `FixedUInt`'s own `ConditionallySelectable`).
// Soundness: both `a` and `b` carry the "value != 0" invariant, so
// the selected value is non-zero regardless of which arm is taken.
impl<T, const N: usize> subtle::ConditionallySelectable
    for NonZeroFixedUInt<T, N, const_num_traits::Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        Self(<FixedUInt<T, N, const_num_traits::Ct> as subtle::ConditionallySelectable>::conditional_select(
            &a.0, &b.0, choice,
        ))
    }
}

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> HasNonZero for FixedUInt<T, N, P> {
        type NonZero = NonZeroFixedUInt<T, N, P>;

        // `Option` shape is branchful at the call site — fine for
        // public inputs, but a secret-derived `self` leaks the "is
        // zero" bit through the `Some`/`None` discriminant. Ct callers
        // route through `CtNonZero::into_nonzero_ct` (below) which
        // returns a masked `CtOption`.
        #[inline]
        fn into_nonzero(self) -> Option<Self::NonZero> {
            if <Self as Zero>::is_zero(&self) {
                None
            } else {
                Some(NonZeroFixedUInt(self))
            }
        }

        #[inline]
        fn nonzero_get(nz: Self::NonZero) -> Self {
            nz.0
        }
    }

    // `DivNonZero` is `Nct`-only because `core::ops::Div for FixedUInt` is
    // `Nct`-only (the long-division body is value-dependent — `if remainder
    // >= divisor` etc. — and doesn't fit `Ct` semantics).
    //
    // Panic-freeness: the API contract ("no `Result` or `.unwrap()` at
    // the caller boundary") is met — the `NonZeroFixedUInt` proof-type
    // discharges the divide-by-zero check statically. But the produced
    // binary still contains a `panic_fmt` symbol because `self / d.0`
    // routes through `const_div_rem`, which retains a runtime
    // divisor-non-zero check whose branch LLVM can't prove unreachable
    // through the `#[repr(transparent)]` wrapper. Consumers who need
    // a *binary-level* panic-free divide should audit downstream.
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize> DivNonZero for FixedUInt<T, N, Nct> {
        type Output = FixedUInt<T, N, Nct>;

        #[inline]
        fn div_nonzero(self, d: Self::NonZero) -> Self::Output {
            self / d.0
        }

        #[inline]
        fn rem_nonzero(self, d: Self::NonZero) -> Self::Output {
            self % d.0
        }
    }
}

// `CtNonZero` — masked-return `into_nonzero` for both personalities;
// the `Choice` mask is value-level and CT-uniform.
impl<T, const N: usize, P: Personality> const_num_traits::CtNonZero for FixedUInt<T, N, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn into_nonzero_ct(self) -> subtle::CtOption<Self::NonZero> {
        use const_num_traits::ops::ct::CtIsZero;
        let zero = self.ct_is_zero();
        // The `!zero` mask gates observation, so consumers only see
        // the wrapper when `self` is actually non-zero.
        subtle::CtOption::new(NonZeroFixedUInt(self), !zero)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::{Ct, Nct};

    type U32 = FixedUInt<u8, 4, Nct>;
    type U32Ct = FixedUInt<u8, 4, Ct>;

    #[test]
    fn into_nonzero_some_for_nonzero() {
        assert!(U32::from(5u32).into_nonzero().is_some());
    }

    #[test]
    fn into_nonzero_none_for_zero() {
        assert!(U32::from(0u32).into_nonzero().is_none());
    }

    #[test]
    fn into_nonzero_works_under_ct_too() {
        assert!(U32Ct::from(5u32).into_nonzero().is_some());
        assert!(U32Ct::from(0u32).into_nonzero().is_none());
    }

    #[test]
    fn nonzero_round_trip() {
        let v = U32::from(42u32);
        let nz = v.into_nonzero().unwrap();
        assert_eq!(<U32 as HasNonZero>::nonzero_get(nz), v);
        assert_eq!(nz.get(), v);
    }

    #[test]
    fn div_rem_nonzero_match_div_rem() {
        let a = U32::from(100u32);
        let m = U32::from(7u32);
        let nz = m.into_nonzero().unwrap();
        assert_eq!(<U32 as DivNonZero>::div_nonzero(a, nz), a / m);
        assert_eq!(<U32 as DivNonZero>::rem_nonzero(a, nz), a % m);
    }

    #[test]
    fn div_rem_nonzero_wider_carrier() {
        // Spot-check a u32-backed carrier to confirm the trait composes
        // across limb-width variants.
        type U128 = FixedUInt<u32, 4, Nct>;
        let a = U128::from(12_345_678u32);
        let m = U128::from(101u32);
        let nz = m.into_nonzero().unwrap();
        assert_eq!(<U128 as DivNonZero>::div_nonzero(a, nz), a / m);
        assert_eq!(<U128 as DivNonZero>::rem_nonzero(a, nz), a % m);
    }

    // Compile-time guard: `DivNonZero for FixedUInt<_, _, Ct>` does NOT
    // exist (Div on FixedUInt is Nct-only). The `HasNonZero` impl stays
    // generic in P — the proof type exists for Ct, it just can't be
    // divided by. `static_assertions::assert_not_impl_any!` fires at
    // compile time if a future `impl DivNonZero for FixedUInt<_, _, Ct>`
    // sneaks in.
    static_assertions::assert_not_impl_any!(
        FixedUInt<u32, 4, const_num_traits::Ct>: DivNonZero
    );

    #[test]
    fn into_nonzero_ct_masks_zero() {
        use const_num_traits::CtNonZero;
        type U32Nct = FixedUInt<u8, 4, Nct>;
        type U32Ct = FixedUInt<u8, 4, Ct>;

        // Nct carrier
        let nz = U32Nct::from(5u32).into_nonzero_ct();
        assert!(bool::from(nz.is_some()));
        assert_eq!(nz.unwrap().get(), U32Nct::from(5u32));

        let z = U32Nct::from(0u32).into_nonzero_ct();
        assert!(!bool::from(z.is_some()));

        // Ct carrier
        let nz_ct: U32Ct = U32Nct::from(42u32).into();
        let opt = nz_ct.into_nonzero_ct();
        assert!(bool::from(opt.is_some()));
        assert_eq!(opt.unwrap().get(), nz_ct);

        let z_ct: U32Ct = U32Nct::from(0u32).into();
        let opt = z_ct.into_nonzero_ct();
        assert!(!bool::from(opt.is_some()));
    }
}
