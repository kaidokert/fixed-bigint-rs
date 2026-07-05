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
//! `core::num::NonZero` is sealed to primitives, so [`NonZeroFixedUInt`]
//! is the `HasNonZero::NonZero` newtype for `FixedUInt`; it is
//! `#[repr(transparent)]` over the inner value.
//!
//! `HasNonZero` covers both personalities (the `!= 0` check is
//! value-level and CT-uniform). `DivNonZero` is `Nct`-only, matching
//! `FixedUInt`'s own `Div`: long division is value-dependent and does
//! not fit constant-time semantics.
//!
//! `into_nonzero` returns `Option`, which is branchful at the call
//! site. Fine for public moduli; secret-derived proofs need a
//! `CtOption`-returning path that lives above this crate.

use super::{FixedUInt, MachineWord};
use crate::machineword::ConstMachineWord;
use const_num_traits::Zero;
use const_num_traits::{DivNonZero, HasNonZero, Nct, Personality};

/// Non-zero `FixedUInt`. Constructed via [`HasNonZero::into_nonzero`].
///
/// `#[repr(transparent)]` over `FixedUInt<T, N, P>` so any
/// `Zeroize` / `Drop` semantics added to `FixedUInt` downstream flow
/// through. Always `Copy` (matches `HasNonZero::NonZero: Copy`).
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NonZeroFixedUInt<T, const N: usize, P: Personality>(FixedUInt<T, N, P>)
where
    T: MachineWord;

// `Debug` impl'd manually because `FixedUInt`'s `Debug` bounds differ by
// personality (Nct needs `T: Debug`, Ct always — see fixeduint.rs:100/108).
// A `#[derive(Debug)]` here adds a uniform `T: Debug` bound that the Ct
// variant doesn't need; spelling them out preserves the existing shape.
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
    /// Recover the underlying `FixedUInt`. Same as
    /// `<FixedUInt<T,N,P> as HasNonZero>::nonzero_get(self)`; offered as
    /// an inherent method for syntactic convenience.
    #[inline]
    pub fn get(self) -> FixedUInt<T, N, P> {
        self.0
    }

    /// # Safety
    /// `value` must be non-zero.
    ///
    /// Crate-internal only — exists to satisfy the upstream
    /// `CtNonZero::into_nonzero_ct` impl pattern, where the unmasked
    /// value is wrapped before the `Choice` mask is applied (so a
    /// reader of a `CtOption::None`-masked result can't observe the
    /// inner state without the explicit `unwrap`). The same shape as
    /// `core::num::NonZero::new_unchecked`. Not exposed publicly
    /// because all other paths (notably the safe
    /// `HasNonZero::into_nonzero`) are reachable without it.
    #[inline]
    pub(crate) const unsafe fn new_unchecked(value: FixedUInt<T, N, P>) -> Self {
        Self(value)
    }
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
        // SAFETY: `FixedUInt::from(1u8)` is statically non-zero.
        unsafe { NonZeroFixedUInt::new_unchecked(FixedUInt::from(1u8)) }
    }
}

// `#[repr(transparent)]` over `FixedUInt`, so `ConditionallySelectable`
// delegates straight through. Restricted to `P = Ct` because
// `FixedUInt`'s own `ConditionallySelectable` impl is `Ct`-only (the
// `subtle` typestate makes no sense for `Nct`). Soundness: both
// branches carry the "value != 0" invariant, so the selected value is
// non-zero regardless of which arm is taken. Needed by
// `subtle::CtOption::unwrap_or` in the masked-returning
// `CtNonZero::into_nonzero_ct` path.
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

// ── CtNonZero (masked-return into_nonzero, secret-modulus path) ──────
//
// Lives in `const_num_traits::ops::typestate::CtNonZero` (not `ops::ct`,
// because it's supertrait `HasNonZero` which lives in typestate.rs).
// Same body shape as the upstream primitive `ct_nonzero!` macro: wrap
// the unmasked value via `new_unchecked` and gate it behind
// `!self.ct_is_zero()`. Both personalities — masking is value-level
// and CT-uniform.
impl<T, const N: usize, P: Personality> const_num_traits::CtNonZero for FixedUInt<T, N, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn into_nonzero_ct(self) -> subtle::CtOption<Self::NonZero> {
        use const_num_traits::ops::ct::CtIsZero;
        let zero = self.ct_is_zero();
        // SAFETY: the `CtOption` mask is `!zero`, so the wrapper is only
        // observable to consumers when the underlying value is genuinely
        // non-zero. Same pattern as `core::num::NonZero::new_unchecked`
        // inside `subtle::CtOption::new(NonZero::new_unchecked(self), !zero)`.
        let nz = unsafe { NonZeroFixedUInt::new_unchecked(self) };
        subtle::CtOption::new(nz, !zero)
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
        // `HasNonZero` is generic in `P` — the non-zero invariant is
        // value-level, no CT-specific construction needed. The Option
        // discriminant at the call site is the existing branchfulness;
        // for secret values, see the module rustdoc.
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

    #[test]
    fn divnonzero_not_impld_for_ct() {
        // Compile-time guard: `DivNonZero for FixedUInt<_, _, Ct>` does
        // NOT exist (Div on FixedUInt is Nct-only). The following SHOULD
        // fail to compile if uncommented:
        //
        //     let a: U32Ct = U32Ct::from(100u32);
        //     let nz: NonZeroFixedUInt<u8, 4, Ct> = a.into_nonzero().unwrap();
        //     let _ = <U32Ct as DivNonZero>::div_nonzero(a, nz);
        //
        // The HasNonZero impl is still generic in P (see
        // `into_nonzero_works_under_ct_too`), so the proof type still
        // exists for Ct carriers — it just can't be divided.
    }

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
