# Changelog

## Unreleased — `experiment/external-const-num-traits`

This branch shifts `fixed-bigint`'s trait surface from the in-tree
`const_numtraits` module onto the standalone
[`const-num-traits`](https://github.com/kaidokert/num-traits) fork (a
const-friendly evolution of upstream `num-traits`). The shape of the
public API is mostly familiar — same trait names, same
operations — but several signatures changed to follow the new
crate's conventions, and a few traits were added or split.

### Breaking changes

* **By-value receivers for the migrated arithmetic surface.**
  `CheckedAdd::checked_add`, `WrappingMul::wrapping_mul`, the
  `Overflowing*` and `Saturating*` families, the bit-shift variants
  (`CheckedShl`, `UnboundedShl`, …), `BorrowingSub`, `CarryingAdd`,
  `CarryingMul`, and the related families now take `self` and
  `Self`-typed arguments by value instead of by reference. Call
  sites change from `x.checked_add(&y)` to `x.checked_add(y)`.
  Generic code that returns `T` may need to restate the result
  type: `T: CheckedMul + Mul<Output = T>` (or
  `T: CheckedMul<Output = T>`). See the new crate's `MIGRATION.md`
  for the full rationale; the short version is that core's inherent
  methods are by-value because primitives are `Copy`, and the new
  crate tracks that exactly.
* **`ToBytes` is by-value, `FromBytes` stays borrowed.**
  `ToBytes::to_le_bytes(self) -> Self::Bytes` and `to_be_bytes(self)`
  take `self` by value (matches the other by-value-receiver changes
  above). `FromBytes::from_le_bytes(bytes: &Self::Bytes) -> Self`
  and `from_be_bytes` stay *borrowed* — the buffer is read, not
  reused as storage, and keeping it borrowed lets variable-length
  types use `type Bytes: ?Sized` with a `[u8]` slice (no allocation).
  This is a deliberate asymmetry; see the new crate's API_BREAKS.md
  entry #5.
* **Bundled-trait splits.** The local crate's "fat" traits were
  split along upstream `num-traits` lines. `ConstZero` → `Zero`
  (methods) + `ConstZero` (the `ZERO` associated constant);
  `ConstOne` similarly. `ConstPowerOfTwo` → `IsPowerOfTwo` +
  `NextPowerOfTwo`. `ConstUnboundedShift` → `UnboundedShl` +
  `UnboundedShr`. `ConstMultiple` → `MultipleOf` + `NextMultipleOf`.
  `ConstIlog` → `Ilog` + `Ilog2` + `Ilog10`. `ConstIsqrt` → `Isqrt`
  + `CheckedIsqrt` (signed-only). `ConstDivCeil` no longer carries
  the checked variant — see "removed" below.
* **`WideningMul` is no longer implemented for `FixedUInt`.**
  Per the upstream design, `WideningMul::Wide` is a single
  double-width primitive (e.g. `u8` → `u16`). Arbitrary-precision
  types like `FixedUInt<T, N>` have no `FixedUInt<T, 2N>` to be
  `Wide`, so the trait is intentionally unimplemented. Use
  `CarryingMul` instead — it returns `(low, high)` natively, which
  is the right shape, and it's already implemented across both
  personalities.
* **`PrimInt` impl on `FixedUInt` removed for now.** External
  `PrimInt` requires `Num + NumCast + Saturating`, which aren't
  implemented on `FixedUInt` yet. `pow` is exposed as an inherent
  method on `FixedUInt<…, Nct>` in the meantime; you can also call
  `pow_impl(v, exp)` directly in const context. Re-adding the
  `PrimInt` bundle is tracked.
* **`Default::default()` on `BytesHolder<T, N>` is now const-callable
  on nightly.** On stable behavior is unchanged. Downstream nightly
  users can write `const X: BytesHolder<u8, 4> = Default::default();`
  directly.
* **`patch_num_traits` is gone.** Its `OverflowingShl`/`OverflowingShr`
  and `WideningMul`/`CarryingMul` types existed only because earlier
  upstream `num-traits` lacked them; the new crate provides them
  directly. Users who imported `fixed_bigint::patch_num_traits::*`
  should switch to `fixed_bigint::const_numtraits::*`.
* **`fixed_bigint::personality` module is gone — the `Ct`/`Nct`
  typestate now lives in `const-num-traits`.** The marker is a
  pure-`core` capability (it depends only on `PhantomData`) and a
  growing number of consumers want it without depending on
  `fixed-bigint`, so it moved upstream. The trait and its tag/marker
  are byte-identical; only the path changed. Downstream:
  `use fixed_bigint::personality::{Ct, Nct, Personality, PersonalityTag};`
  → `use const_num_traits::{Ct, Nct, Personality, PersonalityTag};`,
  and add a direct dep on `const-num-traits` (we deliberately do
  *not* re-export from `fixed_bigint`, to keep downstream coupling
  visible).

### Added

Several traits the local crate didn't carry are now implemented:

* **Fixed-size byte conversion at the API boundary** — four inherent
  methods on `FixedUInt`:
  - `to_le_bytes_fixed<const M>(&self, out: &mut [u8; M]) -> &[u8]`
  - `to_be_bytes_fixed<const M>(&self, out: &mut [u8; M]) -> &[u8]`
  - `from_le_bytes_fixed<const M>(bytes: &[u8; M]) -> Self`
  - `from_be_bytes_fixed<const M>(bytes: &[u8; M]) -> Self`

  These remove the `Result<_, bool>` and the `.unwrap()` at the call
  site that the existing `{to,from}_{le,be}_bytes(…&[u8]…)` methods
  force. Typed `&[u8; M]` parameter + monomorphization-time
  `M >= BYTE_WIDTH` check; wrong-size callers fail at compile time
  with a clear diagnostic, no runtime length validation.

  **API contract is "no panic at the API boundary," not "no
  panic_fmt in the linked binary."** A `cargo nm` audit on
  thumbv7em-none-eabi (`ct-verify/panic-free-audit`) confirms the
  produced `.a` still contains
  `core::slice::copy_from_slice_impl::len_mismatch_fail` →
  `core::panicking::panic_fmt`. Origin: the bodies'
  `chunk.copy_from_slice(word.to_le_bytes().as_ref())` routes
  through `slice::copy_from_slice`'s runtime length check, which
  LLVM cannot elide because both the chunk length and `as_ref().len()`
  are opaque trait-associated values it can't statically equate
  (even though both equal `WORD_SIZE` by construction). The fix
  would be `ptr::copy_nonoverlapping` with a SAFETY proof, but the
  crate's `use-unsafe` feature is scoped specifically to the
  ToBytes/FromBytes `BytesHolder` path where const-generics had no
  other option, not as a general license; without a safe fix from
  upstream, the residual `panic_fmt` stays. Downstream embedded
  crypto consumers that *require* a fully panic-clean binary (e.g.
  `ed25519_heapless`'s AVR linkage gate) cannot rely on these
  methods alone to satisfy that — the upstream
  `slice::copy_from_slice` body limits us.

  Compile-time size check is implemented as a private trait
  (`AssertBufferFits<M>`) with a `const CHECK: () = assert!(...)`
  associated item — not `const { assert!(…) }`, because on nightly
  with `generic_const_exprs` enabled in-fn const blocks referencing
  the const generic become "generic constants" rustc rejects as
  "overly complex." The trait shape sidesteps that and works
  identically on both toolchains.

  Truncation convention for `M > BYTE_WIDTH` mirrors the slice-based
  methods: LE reads the first `BYTE_WIDTH` bytes, BE reads the last.

  Also adds `pub const FixedUInt::BYTE_WIDTH: usize = N * size_of::<T>()`
  so callers can write `let mut buf = [0u8; T::BYTE_WIDTH];` without
  duplicating the byte-width math.

  17 unit tests + 4 doctests cover exact-size + oversized buffers,
  round-trips, cross-validation against the slice-based methods, and
  the `BYTE_WIDTH` array-length ergonomic.
* `PowerOfTwoOps for FixedUInt<T, N, P>` — the five consuming ops
  (`div_pow2`, `rem_pow2`, `is_multiple_of_pow2`,
  `next_multiple_of_pow2`, `checked_next_multiple_of_pow2`) that
  replace `div`/`rem` on a power-of-two divisor with a shift and a
  mask. One impl covers both `Ct` and `Nct` — every body is a shift,
  mask, or addition with no value-dependent branch.

  Construction goes through the upstream safe constructor:

  ```rust
  use const_num_traits::PowerOfTwo;
  let p = PowerOfTwo::<FixedUInt<u32, 8>>::new_checked(value);
  ```

  `PowerOfTwo::new_checked` (`const-num-traits` ≥ PR #7, commit
  `410cfac`) is bounded on `T: IsPowerOfTwo + PrimBits`, both of
  which `FixedUInt` implements, so no glue method is required on
  this side and no `unsafe` crosses into the caller. The `c0nst`
  bounds on the new constructor mean nightly callers get the full
  construction-and-consumption chain in `const` context too. An
  earlier shape of this surface (`fixed_bigint::FixedUInt::as_power_of_two`,
  briefly committed as `143e4c5`) wrapped the upstream `unsafe const
  fn from_exp_unchecked` and was reverted because the crate's
  `use-unsafe` feature is scoped narrowly to the `BytesHolder` path,
  not as a general license; the upstream API change made the workaround
  unnecessary.

  Also adds `FixedUInt::from_power_of_two(p)` as the symmetric
  reconstruction helper (`1 << p.exp()`), and `next_multiple_of_pow2`
  inherits the personality-specific `+` semantic (panic-on-overflow
  under `Nct`, wrap under `Ct`); untrusted-input callers should use
  `checked_next_multiple_of_pow2` instead — the explicit no-panic
  sibling per the design principle "every panicking API ships a
  Try*-style counterpart."

  No `impl PowerOfTwoOps for &FixedUInt<...>`: the trait's
  `PowerOfTwo<Self>` parameter would force a separately-typed proof
  for the borrowed shape. `FixedUInt: Copy` makes deref free, so
  callers use `PowerOfTwoOps::div_pow2(*v, p)`.

  9 tests cover constructor filtering + round-trip, each consuming
  op, the wider-carrier (`FixedUInt<u32, 4>`) limb-boundary case,
  the `checked_*` no-panic sibling, and a nightly empirical-const
  block proving the full chain is const-callable.
* `Odd<FixedUInt>` / `Even<FixedUInt>` compose automatically from the
  upstream typestate (`const_num_traits::Odd::<FixedUInt<...>>::new(v)`,
  `Odd::from_ref(&v)`, `get()`, `Even` ditto). No source change in
  `fixed-bigint` was required — the upstream blanket
  `impl<T: Parity + Copy> Odd<T>` (and the `for<'a> &'a T: Parity`
  bound on `from_ref`) is satisfied by `FixedUInt`'s `Parity` impl
  plus the `&FixedUInt: Parity` blanket the typestate sweep added
  to `const-num-traits`. The composition is frozen against
  regression by `tests/odd_even_typestate.rs` (8 tests covering
  owned/borrowed construction, both personalities, narrow + wide
  carriers, and a proof-consumer call-site pattern). Downstream
  consumers (notably `modmath`'s `Field::from_odd_modulus` plan in
  `PANIC_FREE_REQUESTS.md`) get the typestate-based infallible
  constructor pattern with no fixed-bigint-side glue.
* `Parity` (`is_odd`, `is_even`) — both personalities.
* `HighestOne` / `LowestOne` — both personalities; index of the
  highest/lowest set bit, `None` for zero.
* `BitWidth` — `BIT_SIZE - leading_zeros`; both personalities.
* `IsolateHighestOne` / `IsolateLowestOne` — mask the value down to
  just its highest/lowest set bit; both personalities. The lowest
  variant uses the classic `self & self.wrapping_neg()` trick.
* `ShlExact` / `ShrExact` — reversible shifts; `None` if any bits
  would be dropped.
* `FunnelShl` / `FunnelShr` — concatenated-double-width shifts;
  both personalities (the `n >= BIT_SIZE` panic is value-independent).
* `DepositBits` / `ExtractBits` — PDEP/PEXT-style bit movement; gated
  on `Nct` because the natural implementation iterates per set bit of
  the mask, which is value-dependent.
* `Strict{Add,Sub,Mul,Div,Rem,Shl,Shr,Pow}` — panic-on-overflow
  flavor; gated on `Nct` because the panic semantic is intrinsically
  value-dependent. `StrictNeg`/`StrictAbs` are deliberately not
  implemented (they require a `Neg` supertrait `FixedUInt` doesn't
  have, and for unsigned types `strict_neg` only succeeds on `0`).

Every migrated trait above is also implemented for `&FixedUInt<…>` so
call sites can pass references generically (`fn f<T: CheckedMul>(…)`
with `T = &FixedUInt<…>` Just Works), and `(&x).checked_add(&y)`
matches the ergonomics of the operator-backed `&T` impls without
the explicit deref litter.

### Removed

* `Truncate` checked/saturating variants and `CastSigned`/`CastUnsigned`
  checked/saturating variants — these were exact duplicates of the
  generic cast traits. Use `CheckedCast::<T>`, `SaturatingCast::<T>`,
  `StrictCast::<T>`, `WrappingCast::<T>` instead (see upstream
  `MIGRATION.md` §2.6).
* The local `Const*` trait *aliases* — the canonical names from the
  external crate (`CheckedAdd`, `WrappingMul`, etc.) are now used
  directly. `ConstZero` and `ConstOne` retain their names because
  upstream `num-traits` uses them for the associated-`const` form;
  see the note on `Const*` vs `c0nst trait` below.

### Notes

#### `Const*` vs `c0nst trait` — they mean different things

* `Zero` is a `c0nst trait` (with methods `zero()`, `is_zero()`,
  `set_zero()`). The "c0nst" lets those methods be called in `const`
  context on nightly.
* `ConstZero` is a regular trait — its only item is an associated
  `const ZERO: Self`. The "Const" here refers to that associated
  *constant*, not to the trait being const-callable.

You implement `Zero` for the methods, `ConstZero` for the constant.
Most downstream code that wants "the zero of this type at compile
time" should reach for `<T as ConstZero>::ZERO`. Same story for
`One` / `ConstOne`.

#### `const fn` evaluability

The migrated trait surface is uniformly wrapped in the `c0nst::c0nst!`
macro, which renders impls as `impl Trait for X` on stable and
`impl const Trait for X` on nightly with the `nightly` feature.
Nightly builds also enable `feature(const_default)`, so
`Default::default()` works in `const` context for our
`BytesHolder<T, N>` type (and for the existing nightly-only
`ConstBytesHolder<N>`).

Three inherent shims — `checked_div_ceil`, `checked_isqrt`, `pow` —
stay non-`const` because the `c0nst` macro doesn't translate
`[c0nst]` bounds on inherent `impl` blocks. Each has a free
`*_impl` (or trait-method) const-callable parallel that downstream
nightly users can call directly:

```rust
// non-const inherent (works everywhere)
let r = x.pow(8);

// const (nightly)
const R: U16 = fixed_bigint::fixeduint::pow_impl(X, 8);
```

`pow_impl`, `checked_div_ceil_impl`, and `<T as Isqrt>::isqrt(v)` are
the const-context entry points.

#### Per-architecture impl gating

* The `subtle`-driven constant-time path (the `Ct` personality) stays
  exactly where it was. `Parity`, `HighestOne`, `LowestOne`,
  `BitWidth`, the `IsolateOne` family, `ShlExact`/`ShrExact`, and the
  funnel shifts all implement uniformly across both personalities —
  none of them branch on `Self` values.
* `Strict*`, `DepositBits`/`ExtractBits`, and `CheckedDiv`/`CheckedRem`
  stay `Nct`-only: each has either a value-dependent panic or a
  loop whose iteration count is value-dependent, neither of which
  fits constant-time semantics.

### Migration checklist for downstream crates

1. Bump the toolchain pin to **≥ 1.86** if you weren't already there.
2. Drop the `&` from call sites for the migrated arithmetic methods:
   `x.checked_add(&y)` → `x.checked_add(y)`. Sites that use the
   `core::ops::Add` operator family don't change.
3. For generic functions bounded on the arithmetic traits that
   return `T`, add the result-type restatement:
   `T: CheckedMul + Mul<Output = T>`.
4. If you were implementing the traits on your own type: split the
   bundled impls along the lines in the "Breaking changes" section;
   add `type Output = Self;` to your impls of the fresh-`Output`
   traits per the new crate's §2.3.
5. If you were calling anything in `fixed_bigint::patch_num_traits`,
   switch the path to `fixed_bigint::const_numtraits`.
6. If you implemented `WideningMul` for a wrapper around `FixedUInt`,
   switch to `CarryingMul` — see §2.4 of the new crate's
   `MIGRATION.md`.
