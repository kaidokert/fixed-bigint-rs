//! Personality typestate for [`FixedUInt`](crate::FixedUInt).
//!
//! The personality is a zero-size marker generic on [`FixedUInt`] that selects
//! which implementations of operation primitives are picked at
//! monomorphization. Two personalities ship with the crate:
//!
//! - [`Nct`] (default): standard "non-constant-time" implementation.
//! - [`Ct`]: constant-time implementation. Slower bodies whose timing is
//!   independent of operand values, defensible against an adversarial
//!   optimizer. Used by signing paths and any code handling secret values.
//!
//! ## Const-eval dispatch via `match P::TAG`
//!
//! Composite `const fn` methods that need to dispatch on personality can
//! `match` on the [`PersonalityTag`] associated constant:
//!
//! ```ignore
//! const fn dispatched<P: Personality>(x: u32) -> u32 {
//!     match P::TAG {
//!         PersonalityTag::Nct => fast_body(x),
//!         PersonalityTag::Ct  => ct_body(x),
//!     }
//! }
//! ```
//!
//! Trait *method* calls (e.g. `P::widening_mul(x, y)`) require unstable
//! `const_trait_impl` in const contexts and are not used by this crate. Tag
//! dispatch works on stable today and composes through multi-level generic
//! `const fn` chains without loss of const-eval.

use core::marker::PhantomData;

mod sealed {
    pub trait Sealed {}
}

/// Marker trait for personalities. Sealed — implementations live in this
/// crate. Downstream code uses the [`Nct`] and [`Ct`] types directly or
/// writes `match P::TAG` dispatch using [`PersonalityTag`].
pub trait Personality: sealed::Sealed + Copy + 'static {
    /// Compile-time tag used by `const fn` dispatch:
    /// `match P::TAG { PersonalityTag::Nct => …, PersonalityTag::Ct => … }`.
    const TAG: PersonalityTag;
}

/// Compile-time tag identifying the active personality. Returned by
/// [`Personality::TAG`] and used as the discriminant for `match P::TAG`
/// dispatch in `const fn` bodies.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum PersonalityTag {
    /// Non-constant-time.
    Nct,
    /// Constant-time. Defensible against optimizer-introduced timing leaks.
    Ct,
}

/// Non-constant-time marker. Default personality for [`FixedUInt`].
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct Nct;
impl sealed::Sealed for Nct {}
impl Personality for Nct {
    const TAG: PersonalityTag = PersonalityTag::Nct;
}

/// Constant-time marker.
///
/// Selects constant-time implementations of operation primitives — bodies
/// whose execution time and memory access pattern do not depend on operand
/// values. Appropriate for code that handles secret values (signing,
/// scalar multiplication on secret scalars, Montgomery multiplication on
/// secret operands).
///
/// Calls to `subtle::ConditionallySelectable`, `ConstantTimeEq`, and
/// related traits are only available for [`FixedUInt`]<_, _, Ct>` — wrong-
/// variant calls become compile errors, not silent NCT execution.
///
/// [`FixedUInt`]: crate::FixedUInt
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct Ct;
impl sealed::Sealed for Ct {}
impl Personality for Ct {
    const TAG: PersonalityTag = PersonalityTag::Ct;
}

/// PhantomData helper for storing a personality marker as a zero-size field.
/// Use as `_p: PersonalityMarker<P>` in struct definitions.
pub type PersonalityMarker<P> = PhantomData<fn() -> P>;
