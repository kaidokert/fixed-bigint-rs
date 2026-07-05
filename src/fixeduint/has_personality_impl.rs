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

//! `HasPersonality` projection for FixedUInt: the carrier's declared
//! personality is its type parameter, so downstream personality gates
//! (`T: HasPersonality<P = Nct>`) resolve without naming FixedUInt.

use super::{FixedUInt, MachineWord};
use const_num_traits::{HasPersonality, Personality};

impl<T: MachineWord, const N: usize, P: Personality> HasPersonality for FixedUInt<T, N, P> {
    type P = P;
}

#[cfg(test)]
mod tests {
    use const_num_traits::{Ct, HasPersonality, Nct};

    type U64 = crate::FixedUInt<u32, 2>;
    type U64Ct = crate::FixedUInt<u32, 2, Ct>;

    #[test]
    fn projects_declared_personality() {
        fn assert_nct<T: HasPersonality<P = Nct>>() {}
        fn assert_ct<T: HasPersonality<P = Ct>>() {}
        assert_nct::<U64>();
        assert_ct::<U64Ct>();
    }
}
