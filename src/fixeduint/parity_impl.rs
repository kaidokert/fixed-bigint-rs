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

//! `Parity` and `CtParity` implementations for FixedUInt.
//!
//! Parity is a pure low-bit query: `is_odd` ↔ LSB of word 0 is 1.
//! Branchless on both personalities; safe to implement uniformly.
//!
//! `CtParity` (`ct_is_odd` / `ct_is_even`) is the masked counterpart;
//! it routes the LSB-vs-zero comparison through `subtle::ConstantTimeEq`
//! rather than `!=`, so the returned `Choice` stays masked under both
//! `Nct` and `Ct` callers — `Odd::<FixedUInt<...>>::new_ct(v)` (the
//! downstream consumer in `const-num-traits/src/ops/typestate.rs`) gets
//! its `CtOption`-shaped construction path for free.

use super::{FixedUInt, MachineWord};
use crate::machineword::ConstMachineWord;
use const_num_traits::Parity;
use const_num_traits::Personality;
use const_num_traits::ops::ct::CtParity;
use subtle::{Choice, ConstantTimeEq};

c0nst::c0nst! {
    c0nst impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> Parity for FixedUInt<T, N, P> {
        fn is_odd(self) -> bool {
            // N=0 is a degenerate (zero-word) configuration; treat as even.
            // Otherwise parity lives entirely in the LSB of word 0.
            if N == 0 {
                false
            } else {
                (self.array[0] & <T as const_num_traits::ConstOne>::ONE)
                    != <T as const_num_traits::ConstZero>::ZERO
            }
        }
        fn is_even(self) -> bool {
            !<Self as Parity>::is_odd(self)
        }
    }

    // The reference-receiver impl is provided by const_num_traits's blanket
    // `impl<T: Parity + Copy> Parity for &T` (the D1 fix from the typestate
    // synthesis). Manually impl'ing it here now conflicts (E0119).
}

// `CtParity` is **not** a `c0nst trait` upstream — `subtle::Choice`
// constructors aren't `const fn` yet (the upstream module doc spells this
// out: "plain (never-const) traits: subtle's constructors are not const
// fn"). So the impl is a plain `impl`, not wrapped in `c0nst::c0nst!`.
impl<T, const N: usize, P: Personality> CtParity for FixedUInt<T, N, P>
where
    T: MachineWord + ConstantTimeEq,
{
    /// LSB of word 0, masked through `subtle::ConstantTimeEq` against
    /// `ZERO`. Same body for both personalities — under `Nct`, the
    /// branchless form is still correct, just unnecessary for CT
    /// hygiene; under `Ct`, this is the path that keeps the result
    /// masked all the way to `Odd::new_ct`.
    fn ct_is_odd(&self) -> Choice {
        if N == 0 {
            // Degenerate (zero-word) configuration; treat as even.
            return Choice::from(0);
        }
        let lsb = self.array[0] & <T as const_num_traits::ConstOne>::ONE;
        // `Choice::TRUE` when `lsb != 0`.
        !lsb.ct_eq(&<T as const_num_traits::ConstZero>::ZERO)
    }

    fn ct_is_even(&self) -> Choice {
        !<Self as CtParity>::ct_is_odd(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::{Ct, Nct};

    type U16Nct = FixedUInt<u8, 2, Nct>;
    type U16Ct = FixedUInt<u8, 2, Ct>;

    #[test]
    fn parity_nct() {
        assert!(Parity::is_odd(U16Nct::from(1u8)));
        assert!(Parity::is_odd(U16Nct::from(3u8)));
        assert!(Parity::is_odd(U16Nct::from(0xFFFFu16)));
        assert!(!Parity::is_odd(U16Nct::from(0u8)));
        assert!(!Parity::is_odd(U16Nct::from(2u8)));
        assert!(!Parity::is_odd(U16Nct::from(0xFFFEu16)));

        assert!(Parity::is_even(U16Nct::from(0u8)));
        assert!(!Parity::is_even(U16Nct::from(1u8)));
    }

    #[test]
    fn parity_ct() {
        let one_ct: U16Ct = FixedUInt::<u8, 2, Nct>::from(1u8).into();
        let two_ct: U16Ct = FixedUInt::<u8, 2, Nct>::from(2u8).into();
        assert!(Parity::is_odd(one_ct));
        assert!(Parity::is_even(two_ct));
    }

    #[test]
    #[allow(clippy::needless_borrows_for_generic_args)]
    fn parity_ref() {
        let v = U16Nct::from(7u8);
        assert!(Parity::is_odd(&v));
        assert!(!Parity::is_even(&v));
    }

    // --- Empirical const-evaluability proofs --------------------------------
    use crate::machineword::ConstMachineWord;
    use const_num_traits::Personality;

    c0nst::c0nst! {
        pub c0nst fn const_is_odd<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> bool {
            Parity::is_odd(v)
        }
        pub c0nst fn const_is_even<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality>(v: FixedUInt<T, N, P>) -> bool {
            Parity::is_even(v)
        }
    }

    #[test]
    fn nightly_const_eval_parity() {
        // runtime smoke
        assert!(const_is_odd(U16Nct::from(7u8)));
        assert!(const_is_even(U16Nct::from(8u8)));

        #[cfg(feature = "nightly")]
        {
            const ODD: U16Nct = FixedUInt::from_array([7, 0]);
            const EVEN: U16Nct = FixedUInt::from_array([8, 0]);
            const IS_ODD: bool = const_is_odd(ODD);
            const IS_EVEN: bool = const_is_even(EVEN);
            const IS_ODD_OF_EVEN: bool = const_is_odd(EVEN);
            assert!(IS_ODD);
            assert!(IS_EVEN);
            assert!(!IS_ODD_OF_EVEN);
        }
    }

    // ── CtParity (masked-return parity) ─────────────────────────────────

    #[test]
    fn ct_parity_nct() {
        // Returns `Choice` regardless of personality; convert at the
        // assertion site to compare.
        assert!(bool::from(CtParity::ct_is_odd(&U16Nct::from(1u8))));
        assert!(bool::from(CtParity::ct_is_odd(&U16Nct::from(3u8))));
        assert!(bool::from(CtParity::ct_is_odd(&U16Nct::from(0xFFFFu16))));
        assert!(!bool::from(CtParity::ct_is_odd(&U16Nct::from(0u8))));
        assert!(!bool::from(CtParity::ct_is_odd(&U16Nct::from(2u8))));

        assert!(bool::from(CtParity::ct_is_even(&U16Nct::from(0u8))));
        assert!(!bool::from(CtParity::ct_is_even(&U16Nct::from(1u8))));
    }

    #[test]
    fn ct_parity_ct() {
        let one_ct: U16Ct = FixedUInt::<u8, 2, Nct>::from(1u8).into();
        let two_ct: U16Ct = FixedUInt::<u8, 2, Nct>::from(2u8).into();
        assert!(bool::from(CtParity::ct_is_odd(&one_ct)));
        assert!(bool::from(CtParity::ct_is_even(&two_ct)));
    }

    #[test]
    fn ct_parity_agrees_with_parity() {
        // The masked-return and plain forms must agree on truth value
        // for every input. Sweep a handful of representative values
        // (full 16-bit sweep is overkill but cheap).
        for v in [
            0u16, 1, 2, 3, 7, 8, 0xFE, 0xFF, 0x100, 0x101, 0xFFFE, 0xFFFF,
        ] {
            let nct = U16Nct::from(v);
            let ct: U16Ct = U16Nct::from(v).into();
            assert_eq!(
                bool::from(CtParity::ct_is_odd(&nct)),
                Parity::is_odd(nct),
                "Nct ct_is_odd disagrees with is_odd at v={v}"
            );
            assert_eq!(
                bool::from(CtParity::ct_is_odd(&ct)),
                Parity::is_odd(ct),
                "Ct ct_is_odd disagrees with is_odd at v={v}"
            );
        }
    }

    /// `Odd::<FixedUInt<_, _, Ct>>::new_ct(n)` round-trips — exercises the
    /// upstream typestate construction path on the Ct personality.
    #[test]
    fn odd_new_ct_round_trips_for_ct_carrier() {
        use const_num_traits::Odd;

        let odd_ct: U16Ct = FixedUInt::<u8, 2, Nct>::from(7u8).into();
        let even_ct: U16Ct = FixedUInt::<u8, 2, Nct>::from(8u8).into();

        let p_odd = Odd::<U16Ct>::new_ct(odd_ct);
        let p_even = Odd::<U16Ct>::new_ct(even_ct);

        assert!(
            bool::from(p_odd.is_some()),
            "Odd::new_ct(7) should mask Some"
        );
        assert!(
            !bool::from(p_even.is_some()),
            "Odd::new_ct(8) should mask None"
        );

        // Round-trip: unwrap the masked Some, then check the inner value
        // matches the input.
        let recovered = p_odd.unwrap();
        assert_eq!(recovered.get(), odd_ct);
    }
}
