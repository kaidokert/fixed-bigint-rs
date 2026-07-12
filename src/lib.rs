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
//!
//! `FixedUInt<T, N, P>` is `N` limbs of a primitive `T` (`u8`/`u16`/`u32`/`u64`)
//! with a compile-time `Personality` (`Nct` or `Ct`) that selects between
//! value-dependent and constant-time impl bodies at every operator.
//!
//! Basic usage:
//! ```
//! use fixed_bigint::FixedUInt;
//!
//! let a : FixedUInt<u8,2> = 200u8.into();
//! assert_eq!( a + a , 400u16.into() );
//! assert_eq!( a * &100u8.into(), 20000u16.into() )
//! ```
//!
//! With the `num-traits` feature (default), `FixedUInt` also implements
//! `num_integer::Integer` and the `num_traits::PrimInt` bundle:
//! ```
//! # #[cfg(feature = "num-traits")] {
//! use fixed_bigint::FixedUInt;
//! use num_integer::Integer;
//!
//! let a : FixedUInt<u8,2> = 400u16.into();
//! assert_eq!( a.is_multiple_of( &(8u8.into()) ) , true );
//! assert_eq!( a.gcd( &(300u16.into() )) , 100u8.into() );
//! assert_eq!( a.lcm( &(440u16.into() )) , 4400u16.into() );
//! # }
//! ```

/// Fixed-size big integer implementation
pub mod fixeduint;

/// Machine word and doubleword
mod machineword;

/// Fixed-capacity, runtime-length bignum sketch. Parked; see the module
/// header for the design record.
#[cfg(feature = "heapless-runtime-len")]
pub mod heapless;

pub use crate::fixeduint::{FixedUInt, NonZeroFixedUInt};
pub use crate::machineword::MachineWord;

#[cfg(feature = "heapless-runtime-len")]
pub use crate::heapless::HeaplessBigInt;
