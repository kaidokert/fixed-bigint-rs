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

### Added

Several traits the local crate didn't carry are now implemented:

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
