//! Curated re-export of the external `const-num-traits` crate.
//! Internal code writes `use crate::const_numtraits::Zero` etc.
//! without spelling the external crate path.

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
pub use ::const_num_traits::{Ilog, Ilog2, Ilog10, Isqrt};

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

// Highest/lowest set-bit index + masks.
pub use ::const_num_traits::{
    BitWidth, HighestOne, IsolateHighestOne, IsolateLowestOne, LowestOne, ShlExact, ShrExact,
};

// Funnel shifts + PDEP/PEXT-style bit movement.
pub use ::const_num_traits::{DepositBits, ExtractBits, FunnelShl, FunnelShr};

// Strict-arithmetic family (panic-on-overflow).
pub use ::const_num_traits::{
    StrictAdd, StrictDiv, StrictMul, StrictPow, StrictRem, StrictShl, StrictShr, StrictSub,
};

// Cast traits.
pub use ::const_num_traits::{FromPrimitive, NumCast, ToPrimitive};

// Unbounded shifts — split.
pub use ::const_num_traits::{UnboundedShl, UnboundedShr};
