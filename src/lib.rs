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
#![cfg_attr(
    feature = "nightly",
    feature(
        const_trait_impl,
        const_ops,
        const_cmp,
        const_convert,
        const_default,
        const_clone,
        generic_const_exprs,
        const_unsigned_bigint_helpers,
        widening_mul
    )
)]
#![cfg_attr(feature = "nightly", allow(incomplete_features))]

//! A fixed-size big integer implementation, unsigned only.
//! [FixedUInt] implements a [num_traits::PrimInt] trait, mimicking built-in `u8`, `u16` and `u32` types.
//! [num_integer::Integer] is also implemented.
//!
//! Simple usage example:
//! ```
//! use fixed_bigint::FixedUInt;
//!
//! let a : FixedUInt<u8,2> = 200u8.into();
//! assert_eq!( a + a , 400u16.into() );
//! assert_eq!( a * &100u8.into(), 20000u16.into() )
//! ```
//!
//! Use Integer trait:
//! ```
//! use fixed_bigint::FixedUInt;
//! use num_integer::Integer;
//!
//! let a : FixedUInt<u8,2> = 400u16.into();
//! assert_eq!( a.is_multiple_of( &(8u8.into()) ) , true );
//! assert_eq!( a.gcd( &(300u16.into() )) , 100u8.into() );
//! assert_eq!( a.lcm( &(440u16.into() )) , 4400u16.into() );
//! ```

/// Re-export num_traits crate
pub use num_traits;

/// Re-export num_integer crate
pub use num_integer;

/// Fixed-size big integer implementation
pub mod fixeduint;

/// Bits that should be in num_traits
pub mod patch_num_traits;

/// Constant versions of num_traits
pub mod const_numtraits;

/// Fused multiply-accumulate row operations
pub mod mul_acc_ops;

/// Machine word and doubleword
mod machineword;

pub use crate::mul_acc_ops::MulAccOps;
pub use crate::fixeduint::FixedUInt;
pub use crate::machineword::MachineWord;
