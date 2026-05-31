//! Compile-time enforcement of the personality typestate's negative
//! guarantees. Each `assert_not_impl_any!` fails the build if the listed
//! trait is implemented for the listed type, so a regression in the
//! trait-bound surface fails CI instead of silently passing the
//! commented-out "SHOULD fail to compile" blocks in
//! `tests/personality_integration.rs`.

use core::fmt::{Display, LowerHex, UpperHex};
use fixed_bigint::personality::{Ct, Nct};
use fixed_bigint::FixedUInt;
use static_assertions::assert_not_impl_any;
use subtle::{ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

// Nct lacks the CT comparison traits — those are reserved for Ct so
// secret-handling call sites must opt in via the typestate.
assert_not_impl_any!(FixedUInt<u32, 4, Nct>: ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess);

// Ct cannot be formatted with Display / LowerHex / UpperHex — these
// would expose limb contents in panics, logs, or `dbg!`. Callers must
// `forget_ct()` first, making the leak explicit and greppable.
assert_not_impl_any!(FixedUInt<u32, 4, Ct>: Display, LowerHex, UpperHex);

// Ct -> Nct is not `From`/`Into`. Going from CT to non-CT is a privilege
// escalation and must use the named `forget_ct()` method.
assert_not_impl_any!(FixedUInt<u32, 4, Nct>: From<FixedUInt<u32, 4, Ct>>);

// Nct -> Ct, in contrast, is `From`/`Into` (lossless invariant
// tightening). This regular `#[test]` doubles as a positive-direction
// sanity check so a future change that accidentally removed that impl
// would surface here too.
#[test]
fn nct_to_ct_into_is_available() {
    let n: FixedUInt<u32, 4, Nct> = FixedUInt::from([1u32, 2, 3, 4]);
    let _c: FixedUInt<u32, 4, Ct> = n.into();
}
