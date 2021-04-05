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

#[cfg(test)]
use fixed_bigint::FixedUInt as Bn;

use num_traits::FromPrimitive;
use num_traits::Zero;

type Bn16 = Bn<u16, 8>;

#[test]
fn test_zero() {
    let n1 = Bn16::new();
    assert!(n1.is_zero());
    assert!(Bn16::from_u8(0).unwrap().is_zero());
    assert!(!Bn16::from_u8(1).unwrap().is_zero());
    let n2 = Bn16::zero();
    assert_eq!(n1, n2);
}

#[test]
fn test_min_max() {
    fn _test_minmax<BN: num_traits::PrimInt, REF: num_traits::PrimInt>() {
        let min = BN::min_value().to_u64().unwrap();
        let ref_min = REF::min_value().to_u64().unwrap();
        let max = BN::max_value().to_u64().unwrap();
        let ref_max = REF::max_value().to_u64().unwrap();
        assert_eq!(min, ref_min);
        assert_eq!(max, ref_max);
    }

    _test_minmax::<Bn<u8, 1>, u8>();
    _test_minmax::<Bn<u8, 2>, u16>();
    _test_minmax::<Bn<u16, 1>, u16>();
    _test_minmax::<Bn<u8, 4>, u32>();
    _test_minmax::<Bn<u16, 2>, u32>();
    _test_minmax::<Bn<u32, 1>, u32>();
    _test_minmax::<Bn<u8, 8>, u64>();
    _test_minmax::<Bn<u16, 4>, u64>();
    _test_minmax::<Bn<u32, 2>, u64>();
}
