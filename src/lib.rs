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

#![no_std]

//! A fixed-size big integer implementation, unsigned only.
//! [FixedUInt] implements a [num_traits::PrimInt] trait, mimicking built-in `u8`, `u16` and `u32` types.
//!
//! Simple usage example:
//! ```
//! use fixed_bigint::FixedUInt;
//!
//! let a : FixedUInt<u8,2> = 200u8.into();
//! assert_eq!( a + a , 400u16.into() );
//! assert_eq!( a * &100u8.into(), 20000u16.into() )
//! ```

/// Re-export num_traits crate
pub use num_traits;

/// Fixed-size big integer implementation
pub mod fixeduint;

/// Bits that should be in num_traits
pub mod patch_num_traits;

/// Machine word and doubleword
mod machineword;

pub use crate::fixeduint::FixedUInt;
