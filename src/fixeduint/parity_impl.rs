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

//! `Parity` implementation for FixedUInt.
//!
//! Parity is a pure low-bit query: `is_odd` ↔ LSB of word 0 is 1.
//! Branchless on both personalities; safe to implement uniformly.

use super::{FixedUInt, MachineWord};
use crate::const_numtraits::Parity;
use crate::machineword::ConstMachineWord;
use crate::personality::Personality;

c0nst::c0nst! {
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst Parity for FixedUInt<T, N, P> {
        fn is_odd(self) -> bool {
            // N=0 is a degenerate (zero-word) configuration; treat as even.
            // Otherwise parity lives entirely in the LSB of word 0.
            if N == 0 {
                false
            } else {
                (self.array[0] & <T as crate::const_numtraits::ConstOne>::ONE)
                    != <T as crate::const_numtraits::ConstZero>::ZERO
            }
        }
        fn is_even(self) -> bool {
            !<Self as Parity>::is_odd(self)
        }
    }

    // Reference-receiver mirror (see add_sub_impl.rs for rationale).
    impl<T: [c0nst] ConstMachineWord + MachineWord, const N: usize, P: Personality> c0nst Parity for &FixedUInt<T, N, P> {
        fn is_odd(self) -> bool {
            <FixedUInt<T, N, P> as Parity>::is_odd(*self)
        }
        fn is_even(self) -> bool {
            <FixedUInt<T, N, P> as Parity>::is_even(*self)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::personality::{Ct, Nct};

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
    fn parity_ref() {
        let v = U16Nct::from(7u8);
        assert!(Parity::is_odd(&v));
        assert!(!Parity::is_even(&v));
    }

    // --- Empirical const-evaluability proofs --------------------------------
    use crate::machineword::ConstMachineWord;
    use crate::personality::Personality;

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
}
