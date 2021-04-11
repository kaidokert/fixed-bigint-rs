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

#[test]
fn test_num_assign_simple() {
    fn test<
        INT: num_traits::NumAssignOps + core::convert::From<u8> + num_traits::PrimInt + core::fmt::Debug,
    >() {
        let mut a: INT = 2u8.into();
        let b: INT = 3u8.into();
        a += b;
        assert_eq!(a, 5.into());
        a -= b;
        assert_eq!(a, 2.into());
        a *= b;
        assert_eq!(a, 6.into());
        a /= b;
        assert_eq!(a, 2.into());
        a %= b;
        assert_eq!(a, 2.into());
    }
    test::<u8>();
    test::<Bn<u8, 1>>();
    test::<u16>();
    test::<Bn<u16, 1>>();
    test::<Bn<u8, 2>>();
    test::<u32>();
    test::<Bn<u32, 1>>();
    test::<Bn<u16, 2>>();
    test::<Bn<u8, 4>>();
}
