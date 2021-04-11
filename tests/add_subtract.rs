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

use core::num::Wrapping;
#[cfg(test)]
use fixed_bigint::FixedUInt as Bn;

#[test]
fn test_add_variants() {
    fn test_add_variant<
        INT: num_traits::PrimInt
            + num_traits::ops::overflowing::OverflowingAdd
            + num_traits::ops::wrapping::WrappingAdd
            + num_traits::NumAssign
            + num_traits::NumAssignRef
            //+ core::ops::AddAssign<Wrapping<T>>
            + core::ops::AddAssign
            + core::convert::From<u8>
            + core::fmt::Debug,
        REF: num_traits::PrimInt,
    >()
    where
        INT: std::ops::AddAssign<Wrapping<INT>>, //where Wrapping<INT> : std::ops::Add<Output = Wrapping<INT>>
    {
        let one = INT::one();
        let two: INT = 2u8.into();
        let max = INT::max_value();
        let ref_max = REF::max_value().to_u64().unwrap();

        assert_eq!(one.overflowing_add(&one), (2.into(), false));
        assert_eq!(max.overflowing_add(&one), (0.into(), true));
        assert_eq!(max.overflowing_add(&two), (1.into(), true));

        assert_eq!(one.wrapping_add(&one), 2.into());
        assert_eq!(one + one, 2.into());
        assert_eq!(max.wrapping_add(&one), 0.into());
        // would panic: assert_eq!(max + one , 0.into());
        assert_eq!(max.wrapping_add(&two), 1.into());
        // would panic: assert_eq!(max + two , 1.into());

        assert_eq!(one.checked_add(&one), Some(2.into()));
        assert_eq!(max.checked_add(&one), None);
        assert_eq!(max.checked_add(&two), None);

        assert_eq!(one.saturating_add(one), 2.into());
        assert_eq!(max.saturating_add(one), max);
        // Verify with a builtin primitive too
        assert_eq!(max.saturating_add(one).to_u64().unwrap(), ref_max);

        // AddAssign
        let mut val = one;
        val += one;
        assert_eq!(val, 2.into());

        // Wrapping addassign should not panic
        let mut val: Wrapping<INT> = Wrapping(max);
        //val += Wrapping(one);

        // Test assign by ref works too
        let mut val = one;
        let one_ref = &one;
        val += one_ref;
        assert_eq!(val, 2.into());
    }
    test_add_variant::<u8, u8>();
    test_add_variant::<u16, u16>();
    test_add_variant::<u32, u32>();
    test_add_variant::<u64, u64>();

    test_add_variant::<Bn<u8, 1>, u8>();

    test_add_variant::<Bn<u8, 2>, u16>();
    test_add_variant::<Bn<u16, 1>, u16>();

    test_add_variant::<Bn<u8, 4>, u32>();
    test_add_variant::<Bn<u16, 2>, u32>();
    test_add_variant::<Bn<u32, 1>, u32>();

    test_add_variant::<Bn<u8, 8>, u64>();
    test_add_variant::<Bn<u16, 4>, u64>();
    test_add_variant::<Bn<u32, 2>, u64>();
}

#[test]
fn test_subtract() {
    fn test_subtract_variant<
        INT: num_traits::PrimInt
            + num_traits::ops::overflowing::OverflowingSub
            + num_traits::WrappingSub
            + core::convert::From<u8>
            + core::fmt::Debug,
        REF: num_traits::PrimInt,
    >() {
        let zero = INT::zero();
        let one = INT::one();
        let two: INT = 2u8.into();
        let max = INT::max_value();

        assert_eq!(two.overflowing_sub(&one), (1.into(), false));
        assert_eq!(zero.overflowing_sub(&one), (max, true));
        assert_eq!(one.overflowing_sub(&two), (max, true));
        assert_eq!(one.overflowing_sub(&max), (two, true));

        assert_eq!(two.wrapping_sub(&one), 1.into());
        assert_eq!(two - one, 1.into());
        assert_eq!(zero.wrapping_sub(&one), max);
        // would panic: assert_eq!(zero - one , max);
        assert_eq!(one.wrapping_sub(&two), max);
        // would panic: assert_eq!(one - two , max);
        assert_eq!(one.wrapping_sub(&max), two);
        // would panic: assert_eq!(one - max , two);

        assert_eq!(two.checked_sub(&one), Some(1.into()));
        assert_eq!(zero.checked_sub(&one), None);
        assert_eq!(one.checked_sub(&two), None);
        assert_eq!(one.checked_sub(&max), None);

        assert_eq!(two.saturating_sub(one), 1.into());
        assert_eq!(zero.saturating_sub(one), 0.into());
        assert_eq!(one.saturating_sub(two), 0.into());
        assert_eq!(one.saturating_sub(max), 0.into());
    }
    test_subtract_variant::<u8, u8>();
    test_subtract_variant::<u16, u16>();
    test_subtract_variant::<u32, u32>();
    test_subtract_variant::<u64, u64>();

    test_subtract_variant::<Bn<u8, 1>, u8>();

    test_subtract_variant::<Bn<u8, 2>, u16>();
    test_subtract_variant::<Bn<u16, 1>, u16>();

    test_subtract_variant::<Bn<u8, 4>, u32>();
    test_subtract_variant::<Bn<u16, 2>, u32>();
    test_subtract_variant::<Bn<u32, 1>, u32>();

    test_subtract_variant::<Bn<u8, 8>, u64>();
    test_subtract_variant::<Bn<u16, 4>, u64>();
    test_subtract_variant::<Bn<u32, 2>, u64>();
}
