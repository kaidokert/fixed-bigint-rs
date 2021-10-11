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
use fixed_bigint::FixedUInt;

#[test]
fn test_evenodd() {
    fn even_odd<T: num_integer::Integer + From<u8>>() {
        let tests = [(0u8, true), (1u8, false), (2u8, true), (255u8, false)];
        for &(num, even) in &tests {
            let f: T = num.into();
            assert_eq!(f.is_even(), even);
            assert_eq!(f.is_odd(), !even);
        }
    }
    even_odd::<u8>();
    even_odd::<FixedUInt<u8, 1>>();
    even_odd::<FixedUInt<u8, 2>>();
    even_odd::<FixedUInt<u16, 1>>();
}
