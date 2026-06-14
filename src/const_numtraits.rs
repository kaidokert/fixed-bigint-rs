//! EXPERIMENT (branch `experiment/external-const-num-traits`):
//!
//! Curated re-export of the external `const-num-traits` crate. The
//! previous in-tree `Const*` trait surface was bundled (one trait per
//! concept); on this branch we follow the external crate's
//! capability-split design (see `MIGRATION.md` in that crate). This
//! module re-exports the external names so internal code can write
//! `use crate::const_numtraits::Zero` etc. without spelling the
//! external crate path, and downstream consumers see a stable
//! re-export surface during the experiment.

#![allow(unused_imports)]

// Identity traits: now two each.
pub use ::const_num_traits::{ConstOne, ConstZero, One, Zero};

// Bounded.
pub use ::const_num_traits::Bounded;

// Bit / prim-int layer (split: PrimBits is the CT-friendly core).
pub use ::const_num_traits::{PrimBits, PrimInt};

// Arithmetic — checked / wrapping / saturating / overflowing.
pub use ::const_num_traits::{
    CheckedAdd, CheckedDiv, CheckedEuclid, CheckedMul, CheckedPow, CheckedRem, CheckedShl,
    CheckedShr, CheckedSub,
};
pub use ::const_num_traits::{SaturatingAdd, SaturatingMul, SaturatingSub};
pub use ::const_num_traits::{WrappingAdd, WrappingMul, WrappingShl, WrappingShr, WrappingSub};
// Overflowing*: not re-exported from the external crate root yet.
pub use ::const_num_traits::ops::overflowing::{
    OverflowingAdd, OverflowingMul, OverflowingShl, OverflowingShr, OverflowingSub,
};

// Euclid.
pub use ::const_num_traits::Euclid;

// Power-of-two — split.
pub use ::const_num_traits::{IsPowerOfTwo, NextPowerOfTwo};

// Logs / sqrt — split.
pub use ::const_num_traits::{Ilog, Ilog10, Ilog2, Isqrt};

// Rounding / multiples / midpoint / div-ceil.
pub use ::const_num_traits::{DivCeil, Midpoint, MultipleOf, NextMultipleOf};

// AbsDiff.
pub use ::const_num_traits::AbsDiff;

// Bytes.
pub use ::const_num_traits::{FromBytes, ToBytes};

// Bigint helpers (multi-word arithmetic).
pub use ::const_num_traits::{BorrowingSub, CarryingAdd, CarryingMul, WideningMul};

// Parity.
pub use ::const_num_traits::Parity;

// Highest/lowest set-bit index.
pub use ::const_num_traits::{HighestOne, LowestOne};

// Strict-arithmetic family (panic-on-overflow).
pub use ::const_num_traits::{
    StrictAdd, StrictDiv, StrictMul, StrictPow, StrictRem, StrictShl, StrictShr, StrictSub,
};

// Unbounded shifts — split.
pub use ::const_num_traits::{UnboundedShl, UnboundedShr};
