//! `Zero`, `One`, `Default` for `HeaplessBigInt`.
//!
//! - `Zero`: mathematical zero, `len = 0`.
//! - `One`: `len = 1`, `limbs[0] = T::ONE`.
//! - `Default = Zero`. (The CIOS full-CAP zero is a separate constructor,
//!   `cios_accumulator`, not `Default`.)

use super::{AssertCapFits, HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::{Bounded, ConstOne, ConstZero, One, Personality, PersonalityTag, Zero};
use core::marker::PhantomData;

// ── const_num_traits::Zero / One ──

impl<T: MachineWord, const CAP: usize, P: Personality> Zero for HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn zero() -> Self {
        Self::const_zero()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        // Any limb non-zero → non-zero. `Nct` short-circuits; `Ct`
        // OR-folds every limb so timing is value-independent (the returned
        // `bool` is still branchable — see `CtIsZero::ct_is_zero` for the
        // `Choice`-returning form). Limbs beyond `len` are zero by the
        // zero-tail invariant, so scanning `0..len` suffices.
        let n = self.len as usize;
        match P::TAG {
            PersonalityTag::Nct => {
                let mut i = 0;
                while i < n {
                    if !super::is_zero(&self.limbs[i]) {
                        return false;
                    }
                    i += 1;
                }
                true
            }
            PersonalityTag::Ct => {
                let mut acc = zero::<T>();
                let mut i = 0;
                while i < n {
                    acc |= self.limbs[i];
                    i += 1;
                }
                super::is_zero(&acc)
            }
        }
    }

    #[inline]
    fn set_zero(&mut self) {
        *self = <Self as Zero>::zero();
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> One for HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn one() -> Self {
        let () = <Self as AssertCapFits>::CHECK;
        Self::const_one()
    }

    #[inline]
    fn set_one(&mut self) {
        *self = <Self as One>::one();
    }

    #[inline]
    fn is_one(&self) -> bool {
        // `len` is a public shape parameter, so branching on it is fine in
        // both personalities. `Nct` short-circuits the limb scan; `Ct`
        // folds `(limbs[0] ^ 1) | limbs[1] | …` with no early return.
        let n = self.len as usize;
        if n == 0 {
            return false;
        }
        match P::TAG {
            PersonalityTag::Nct => {
                if !<T as const_num_traits::One>::is_one(&self.limbs[0]) {
                    return false;
                }
                let mut i = 1;
                while i < n {
                    if !super::is_zero(&self.limbs[i]) {
                        return false;
                    }
                    i += 1;
                }
                true
            }
            PersonalityTag::Ct => const_is_one_ct(&self.limbs, n),
        }
    }
}

/// CT fold for [`One::is_one`]: `(limbs[0] ^ 1) | limbs[1] | … | limbs[n-1]`,
/// zero iff the value is the canonical one. Timing depends only on the public
/// `len` (`n`), never on where the value first diverges from one. Caller
/// guarantees `n >= 1`.
///
/// Kept out-of-line so the fold's `len`-bounded loop lands in one attestable
/// helper symbol rather than being inlined into its lone caller, where the same
/// loop would read as an un-attestable branch to the CT gate. (FixedUInt's twin
/// unrolls instead, because its bound is the const generic `N`; the heapless
/// bound is a runtime field, so the loop stays a loop and must be attested.)
#[inline(never)]
pub(crate) fn const_is_one_ct<T: MachineWord, const CAP: usize>(
    limbs: &[T; CAP],
    n: usize,
) -> bool {
    let mut acc = limbs[0] ^ <T as ConstOne>::ONE;
    let mut i = 1;
    while i < n {
        acc |= limbs[i];
        i += 1;
    }
    super::is_zero(&acc)
}

impl<T: MachineWord, const CAP: usize, P: Personality> Default for HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn default() -> Self {
        <Self as Zero>::zero()
    }
}

// ── const_num_traits::ConstZero / ConstOne ──
//
// Declared as `const` items so downstream can use them in const
// expressions. `ConstOne::ONE` needs a mutable-array initialisation
// step, which requires a helper `const fn` on stable.

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    #[inline]
    const fn const_zero() -> Self {
        Self {
            limbs: [<T as ConstZero>::ZERO; CAP],
            len: 0,
            _p: PhantomData,
        }
    }

    #[inline]
    const fn const_one() -> Self {
        assert!(CAP >= 1, "HeaplessBigInt::ONE requires CAP >= 1");
        let mut limbs = [<T as ConstZero>::ZERO; CAP];
        limbs[0] = <T as ConstOne>::ONE;
        Self {
            limbs,
            len: 1,
            _p: PhantomData,
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> ConstZero for HeaplessBigInt<T, CAP, P> {
    const ZERO: Self = Self::const_zero();
}

impl<T: MachineWord, const CAP: usize, P: Personality> ConstOne for HeaplessBigInt<T, CAP, P> {
    const ONE: Self = Self::const_one();
}

// ── const_num_traits::Bounded ──
//
// `min = 0` (len 0). `max` is the capacity bound: every one of `CAP` limbs
// saturated, `len = CAP`. This is the one answer `CAP` legitimately sets —
// it is the widest value the storage can represent, not a value width.
#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::Ct;

    type Hc = HeaplessBigInt<u8, 4, Ct>;

    // `One::is_one` on the `Ct` carrier folds through `const_is_one_ct` with no
    // early return; it must still match the predicate exactly, including the
    // `len == 0` (zero) guard and a `1` that sits in a higher limb.
    #[test]
    fn ct_is_one() {
        assert!(<Hc as One>::is_one(&<Hc as One>::one()));
        assert!(!<Hc as One>::is_one(&<Hc as Zero>::zero()));
        assert!(!<Hc as One>::is_one(&Hc::from_limbs([2, 0, 0, 0], 1)));
        assert!(!<Hc as One>::is_one(&Hc::from_limbs([0, 1, 0, 0], 2)));
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Bounded for HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn min_value() -> Self {
        <Self as ConstZero>::ZERO
    }

    #[inline]
    fn max_value() -> Self {
        // `len = CAP` here, so CAP must fit u16 — assert it the same way the
        // shape-setting constructors do, rather than silently truncating.
        let () = <Self as AssertCapFits>::CHECK;
        Self {
            limbs: [<T as Bounded>::max_value(); CAP],
            len: CAP as u16,
            _p: PhantomData,
        }
    }
}
