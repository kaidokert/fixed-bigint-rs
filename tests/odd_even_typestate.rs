//! `Odd<FixedUInt>` / `Even<FixedUInt>` typestate composition.
//!
//! `const-num-traits`'s typestate carries a generic
//! `impl<T: Parity + Copy> Odd<T>` (and the same for `Even`), plus a
//! `from_ref` constructor gated on `for<'a> &'a T: Parity`. `FixedUInt`
//! satisfies both: it impls `Parity` (with a `match P::TAG` body, both
//! personalities), and the upstream blanket `impl<T: Parity + Copy>
//! Parity for &T` covers the borrow.
//!
//! So there is **no work to do inside `fixed-bigint`** to obtain
//! `Odd::<FixedUInt<...>>::new(v)`, `Odd::from_ref(&v)`, and the `Even`
//! counterparts — they compose automatically. This file is the contract
//! test that proves it (and freezes the composition against future
//! regressions in either crate).
//!
//! Why this matters: downstream modmath wants
//! `Field::from_odd_modulus(odd: Odd<T>) -> Self` as the infallible
//! constructor that replaces `Field::new(p).unwrap()` — see
//! `modmath-rs/PANIC_FREE_REQUESTS.md`. The unlock is on the modmath side;
//! this test only certifies that the *upstream* typestate composes with
//! our type, which is the prerequisite.

use const_num_traits::{Even, Odd};
use fixed_bigint::FixedUInt;

type U16 = FixedUInt<u8, 2>;
type U32 = FixedUInt<u32, 1>;

#[test]
fn odd_new_accepts_odd_values_only() {
    assert!(Odd::<U16>::new(U16::from(1u8)).is_some());
    assert!(Odd::<U16>::new(U16::from(3u8)).is_some());
    assert!(Odd::<U16>::new(U16::from(255u8)).is_some());
    assert!(Odd::<U16>::new(U16::from(65535u16)).is_some());

    assert!(Odd::<U16>::new(U16::from(0u8)).is_none());
    assert!(Odd::<U16>::new(U16::from(2u8)).is_none());
    assert!(Odd::<U16>::new(U16::from(254u8)).is_none());
    assert!(Odd::<U16>::new(U16::from(65534u16)).is_none());
}

#[test]
fn even_new_accepts_even_values_only() {
    assert!(Even::<U16>::new(U16::from(0u8)).is_some());
    assert!(Even::<U16>::new(U16::from(2u8)).is_some());
    assert!(Even::<U16>::new(U16::from(254u8)).is_some());
    assert!(Even::<U16>::new(U16::from(65534u16)).is_some());

    assert!(Even::<U16>::new(U16::from(1u8)).is_none());
    assert!(Even::<U16>::new(U16::from(3u8)).is_none());
    assert!(Even::<U16>::new(U16::from(65535u16)).is_none());
}

#[test]
fn odd_get_round_trips() {
    let v = U16::from(255u8);
    let p = Odd::<U16>::new(v).unwrap();
    assert_eq!(p.get(), v);
}

#[test]
fn even_get_round_trips() {
    let v = U16::from(254u8);
    let p = Even::<U16>::new(v).unwrap();
    assert_eq!(p.get(), v);
}

#[test]
fn from_ref_works_borrowed() {
    let odd = U16::from(7u8);
    let even = U16::from(8u8);

    // `Odd::from_ref(&v)` returns `Option<&Odd<T>>` (zero-cost transmute via
    // the upstream blanket `impl Parity for &T`).
    assert!(Odd::<U16>::from_ref(&odd).is_some());
    assert!(Odd::<U16>::from_ref(&even).is_none());

    assert!(Even::<U16>::from_ref(&even).is_some());
    assert!(Even::<U16>::from_ref(&odd).is_none());
}

#[test]
fn wider_carrier_still_composes() {
    // u32-backed FixedUInt (one limb wide), same surface.
    let odd = U32::from(0x8000_0001u32);
    let even = U32::from(0x8000_0002u32);

    assert!(Odd::<U32>::new(odd).is_some());
    assert!(Odd::<U32>::new(even).is_none());
    assert!(Even::<U32>::new(even).is_some());
    assert!(Even::<U32>::new(odd).is_none());

    assert_eq!(Odd::<U32>::new(odd).unwrap().get(), odd);
    assert_eq!(Even::<U32>::new(even).unwrap().get(), even);
}

#[test]
fn ct_personality_composes_too() {
    use const_num_traits::Ct;
    type U16Ct = FixedUInt<u8, 2, Ct>;

    // The upstream blanket only needs `Parity + Copy`, both of which Ct has.
    // No CT-specific construction path is needed here (Ct's `is_odd` is
    // value-independent — it returns a bool, period).
    let odd_ct = U16Ct::from(7u8);
    let even_ct = U16Ct::from(8u8);

    assert!(Odd::<U16Ct>::new(odd_ct).is_some());
    assert!(Even::<U16Ct>::new(even_ct).is_some());
    assert!(Odd::<U16Ct>::new(even_ct).is_none());
    assert!(Even::<U16Ct>::new(odd_ct).is_none());
}

/// Sanity-shaped consumer: a generic function that *requires* an
/// `Odd<FixedUInt>` proof. The point is to demonstrate the call-site
/// pattern downstream consumers (modmath) will use to express
/// "this constructor cannot fail at runtime."
fn requires_odd<T: Copy, const N: usize, P: const_num_traits::Personality>(
    _proof: Odd<FixedUInt<T, N, P>>,
) -> &'static str
where
    T: fixed_bigint::MachineWord,
{
    "ok"
}

#[test]
fn proof_consumer_pattern() {
    let m = U16::from(65521u16);
    // Construction is the *only* fallible step.
    let proof = Odd::<U16>::new(m).expect("65521 is odd");
    // Once the proof exists, downstream calls are infallible — no
    // `unwrap`, no `panic_fmt` in the linked binary.
    assert_eq!(requires_odd(proof), "ok");
}
