//! Behavior shared by every carrier, written once as generic bodies and run
//! for both `FixedUInt` and `HeaplessBigInt`. The bodies live in the topic
//! submodules; the shared `Carrier` surface, the `for_both_carriers!` runner,
//! and the width-pinning constructor live in `harness`.
//!
//! An integration-test root resolves `mod foo` to a sibling `tests/foo.rs`,
//! which cargo would compile as its own test binary — so the submodules sit in
//! `carrier_generic/` (subdirectories are not auto-compiled) and are pulled in
//! by explicit `#[path]`.

#[path = "carrier_generic/harness.rs"]
mod harness;

#[path = "carrier_generic/arithmetic.rs"]
mod arithmetic;
#[path = "carrier_generic/bits_and_compare.rs"]
mod bits_and_compare;
#[path = "carrier_generic/numeric.rs"]
mod numeric;
#[path = "carrier_generic/serialization.rs"]
mod serialization;
#[path = "carrier_generic/shifts_and_bitwise.rs"]
mod shifts_and_bitwise;
