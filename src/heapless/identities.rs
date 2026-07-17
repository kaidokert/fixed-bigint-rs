//! `Zero`, `One`, `Default` for `HeaplessBigInt`.
//!
//! - `Zero`: mathematical zero, `len = 0`.
//! - `One`: `len = 1`, `limbs[0] = T::ONE`.
//! - `Default = Zero`. (The CIOS full-CAP zero is a separate constructor,
//!   `cios_accumulator`, not `Default`.)

use super::{AssertCapFits, HeaplessBigInt, zero};
use crate::MachineWord;
use const_num_traits::{ConstOne, ConstZero, One, Personality, Zero};
use core::marker::PhantomData;

// ── const_num_traits::Zero / One ──

impl<T: MachineWord, const CAP: usize, P: Personality> Zero for HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn zero() -> Self {
        Self::new_zero_with_len(0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        // Value-based: any limb non-zero → non-zero. NCT-implicit (short-
        // circuits on limb content). Ct callers use `CtIsZero::ct_is_zero`
        // via a separate impl (added when needed).
        let mut i = 0;
        while i < self.len as usize {
            if !super::is_zero(&self.limbs[i]) {
                return false;
            }
            i += 1;
        }
        // Zero-tail invariant means limbs beyond len are zero regardless.
        true
    }

    #[inline]
    fn set_zero(&mut self) {
        *self = <Self as Zero>::zero();
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> One for HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn one() -> Self {
        let _ = <Self as AssertCapFits>::CHECK;
        assert!(CAP >= 1, "HeaplessBigInt::one requires CAP >= 1");
        let mut limbs = [zero::<T>(); CAP];
        limbs[0] = <T as ConstOne>::ONE;
        Self {
            limbs,
            len: 1,
            _p: PhantomData,
        }
    }

    #[inline]
    fn set_one(&mut self) {
        *self = <Self as One>::one();
    }

    #[inline]
    fn is_one(&self) -> bool {
        // NCT-implicit content scan.
        if self.len == 0 {
            return false;
        }
        if !<T as const_num_traits::One>::is_one(&self.limbs[0]) {
            return false;
        }
        let mut i = 1;
        while i < self.len as usize {
            if !super::is_zero(&self.limbs[i]) {
                return false;
            }
            i += 1;
        }
        true
    }
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
