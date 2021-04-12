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

// These should be in num_traits
pub trait OverflowingShl: Sized {
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);
}
pub trait OverflowingShr: Sized {
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);
}

macro_rules! overflowing_shift_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(self, rhs: u32) -> ($t, bool) {
                <$t>::$method(self, rhs)
            }
        }
    };
}

overflowing_shift_impl!(OverflowingShl, overflowing_shl, u8);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u16);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u32);
overflowing_shift_impl!(OverflowingShl, overflowing_shl, u64);

overflowing_shift_impl!(OverflowingShr, overflowing_shr, u8);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u16);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u32);
overflowing_shift_impl!(OverflowingShr, overflowing_shr, u64);
