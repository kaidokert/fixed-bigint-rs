# `ct-verify` — constant-time codegen harness for `fixed-bigint`

`fixed-bigint` v0.3.0 introduced a constant-time (CT) personality
typestate. The type system enforces *who can call what* (no `Display`
on `Ct`, no `Div`/`Rem` on `Ct`, only the named `forget_ct()` for the
`Ct → Nct` downgrade) and `tests/personality_negative_guarantees.rs`
uses `static_assertions::assert_not_impl_any!` to make those rules a
compile-time gate.

This harness is the second layer: a codegen-level check that **the
asm emitted for each Ct primitive is actually branch-free** on a set
of priority targets. It runs on every PR alongside the regular test
suite.

## Layered model

```
                       ┌──────────────────────────────────────┐
   Layer 0 (typing) ───►   personality_negative_guarantees.rs │
                       │   compile-fail tests via assert_not_ │
                       │   impl_any! — Ct cannot call Display │
                       │   or Div; Nct cannot call ct_eq.     │
                       └──────────────────────────────────────┘
                                       │
                                       ▼
                       ┌──────────────────────────────────────┐
   Layer 1 (codegen) ──►   ct-verify (this directory)         │
                       │   cross-target asm-grep on each Ct   │
                       │   primitive. Fails CI on any         │
                       │   forbidden conditional control      │
                       │   transfer.                          │
                       └──────────────────────────────────────┘
                                       │
                                       ▼
                       ┌──────────────────────────────────────┐
   Layer 2 (taint)  ───►   pillar deferred (host-side ctgrind │
                       │   / Valgrind, see "Future pillars"   │
                       │   below). Catches secret-derived     │
                       │   memory access patterns that asm-   │
                       │   grep can't see.                    │
                       └──────────────────────────────────────┘
                                       │
                                       ▼
                       ┌──────────────────────────────────────┐
   Layer 3 (timing) ───►   pillar deferred (hardware DWT      │
                       │   on a self-hosted Cortex-M runner). │
                       │   See `ct-fixtures/src/seam.rs`.     │
                       └──────────────────────────────────────┘
```

Each layer catches failure modes the others can't see. They run
independently; all four should pass on every release.

## What gets verified

Three categories of Ct primitive (~170 fixtures total at five
`(T, N)` diagonals each):

**Category A** — methods migrated via `match P::TAG` where the Ct arm
is a distinct body:
`ConstSaturatingAdd/Sub/Mul`, `Shl<usize>`/`Shr<usize>`,
`ConstUnboundedShift::unbounded_shl/shr`, `ConstAbsDiff::abs_diff`,
`ConstPowerOfTwo::is_power_of_two`/`next_power_of_two`,
`ConstBitPrimInt::leading_zeros/trailing_zeros`,
`ConstZero::is_zero`, `ConstOne::is_one`.

**Category B** — Ct-only direct impls that don't exist on Nct:
`ct_checked_add/sub/mul/shl/shr/pow/next_power_of_two`, the four
`subtle::*` trait impls (`ConstantTimeEq`, `ConditionallySelectable`,
`ConstantTimeGreater`, `ConstantTimeLess`), `forget_ct`.

**Category C** — always-CT-by-construction methods (generic over `P`,
but exercised under `Ct` as a regression watch): `Not`/`BitAnd`/
`BitOr`/`BitXor`, `Overflowing*`/`Wrapping*` arithmetic,
`ConstCarryingAdd`, `ConstMidpoint`, `count_ones`/`swap_bytes`/
`reverse_bits`.

## How the gate works

Two techniques hold it together:

1. **`core::hint::black_box`** is the central discipline. `#[no_mangle]
   pub extern "C"` prevents inlining of the *symbol*, but says nothing
   about whether the function *body* has any code in it. Without
   `black_box` at input and output, the optimizer can fold pointer
   loads through, realize the result is "computed" but never observed
   by a caller, and DCE the body to a few ABI-dance instructions.
   The `ct_fix_*` macros in `ct-fixtures/src/lib.rs` wrap both ends
   uniformly. Reviewers MUST reject any fixture written without going
   through these macros — bypass = false-pass.

2. **Pinned codegen settings**. The workspace `[profile.release]` is
   `lto = "fat"`, `codegen-units = 1`, `opt-level = "z"`, `panic =
   "abort"`. Each CI matrix row pins `rustc` to a specific stable
   version (`1.83` at time of writing). Deterministic output means a
   passing PR locks the inspection; a compiler bump that perturbs
   codegen becomes an explicit, reviewable PR rather than silent
   drift.

The driver (`ct-driver`) for each target:

1. Cross-builds `ct-fixtures` to produce `libct_fixtures.a`.
2. Disassembles the archive via `llvm-objdump`.
3. Scopes the scan to `ct_fix__*` and `nct_fix__*` symbols (see
   "Scope" below).
4. Applies per-architecture regex tables (`ct-driver/src/mnemonics.rs`):
   `b.<cond>` / `cbz` / `cbnz` / `tbb` / `tbh` on Thumb,
   `beq` / `bne` / `blt` / `bge` / `bltu` / `bgeu` on RISC-V,
   `br<cc>` / `sbic` / `sbis` / `cpse` on AVR,
   `b.<cond>` / `cbz` / `tbz` on AArch64,
   `j<cc>` on x86_64.
   Architecture-specific allowlists for CT-friendly conditional
   primitives (Thumb IT blocks, AArch64 `csel` / `ccmp`, x86_64
   `cmovcc` / `setcc` / `sbb`).
5. Emits a JSON report and exits non-zero on any violation.

## Scope: only fixture symbols, not helpers

The harness inspects only the `ct_fix__*` / `nct_fix__*` fixture
wrappers, not the `fixed_bigint::*` helper symbols compiled into the
archive. Two reasons:

1. **No call-graph reachability**. A helper like
   `<FixedUInt as Integer>::gcd` exists in the staticlib because the
   crate compiled it, not because any Ct fixture calls it. Disassembly
   alone can't tell which helpers are on a Ct call path.

2. **Public-parameter loop bounds**. Helpers like
   `<FixedUInt as ConditionallySelectable>::conditional_select`
   contain `for i in 0..N` loops that compile to `cmp i, #N; b.lt`.
   That's a forbidden mnemonic by raw regex but perfectly CT-safe
   (`N` is a compile-time constant). Static-pattern analysis can't
   distinguish loop-counter branches from data-dependent ones
   without taint.

The trade-off: a branch-injection regression in a helper that no
fixture transitively calls would not be caught here. Mitigation:

- The fixture wrappers `black_box`-wrap their inputs *and* their
  outputs, so the compiler cannot collapse the body. Whatever the
  fixture eventually computes from those black-boxed inputs is
  observable in the wrapper's emitted asm via the inlined call
  chain — to the extent that LTO at the staticlib stage inlines it.
- **Downstream consumers** (modmath, rsa_heapless, ed25519_heapless,
  pqc) build with their own `lto = "fat"`, which forces every helper
  body to inline into every Ct call site they use. Their own
  CT-verify CI (which they own per "Downstream consumer pattern"
  below) inspects the *post-LTO* bodies of their actual call sites.

A future v2 of this harness can close the gap by adding a host-side
`#[inline(always)]` shim binary that LTO-links each fixture and
re-disassembles. For v1 we accept the limitation.

## Negative controls

`ct-fixtures/src/fixtures_neg.rs` deliberately exercises Nct
primitives that **must** trip the gate. Each has an explicit
data-dependent guard in its wrapper body (`if a == 0` etc.) so the
wrapper itself contains a visible forbidden mnemonic. The driver
asserts every `nct_fix__neg__*` symbol produces ≥1 violation. If a
negative control produces 0 violations, the harness itself is broken
— most likely causes are:

- Compiler unexpectedly inlined the body away or constant-folded
  through `black_box` (unlikely but possible after a major `rustc`
  bump).
- The forbidden-mnemonic regex table for this target is missing a
  spelling the assembler emits (e.g., `.n` suffix variants on Thumb).
- The symbol got stripped by linker / archiver.

The negative-control pass is the harness's self-test. It must pass
on every target.

## Running locally

```
# Build + verify on the host triple (default).
cargo run --release -p ct-driver -- --json-out target/ct-report/host.json

# Specific target.
cargo run --release -p ct-driver -- \
    --target thumbv7em-none-eabi \
    --json-out target/ct-report/thumbv7em-none-eabi.json

# AVR requires nightly + an explicit MCU.
RUSTFLAGS="-C target-cpu=atmega328p" \
    cargo +nightly run --release -p ct-driver -- \
        --target avr-none \
        --json-out target/ct-report/avr-none.json

# List supported targets.
cargo run --release -p ct-driver -- --list-targets

# Re-run on an existing build (no cargo build).
cargo run --release -p ct-driver -- --target thumbv7em-none-eabi --skip-build
```

`rustup` targets must be installed for cross-target runs:
```
rustup target add thumbv7em-none-eabi thumbv6m-none-eabi \
                  riscv32imc-unknown-none-elf riscv32imac-unknown-none-elf \
                  aarch64-unknown-linux-gnu x86_64-unknown-linux-gnu
rustup +nightly component add rust-src       # for AVR build-std
```

`llvm-tools-preview` rustup component must be installed for the
`llvm-objdump` invocation. If you've ever installed `cargo-binutils`,
this is implicit.

## Known target-specific subtleties

### AVR — bool/u8 conversions in fixture ABI

AVR has no `setne`-style instruction, so `u8 != 0` lowers to
`cpi/brne` — a real conditional branch. The first iteration of the
`carrying_add` fixture took `carry_in: u8` and did `!= 0` inside the
wrapper; AVR codegen surfaced this as 4 flagged violations.

The correct fix was to take `carry: bool` directly in the fixture's
ABI and pass it through `black_box`. The fixture wrapper now contains
no boolean materialization on the carry path, and the call into
`ConstCarryingAdd::carrying_add` itself compiles to fully branch-free
code on every target (the primitive `carry as $t` cast on a `bool` is
recognized by LLVM as a no-op normalization, since `bool` has the
required 0-or-1 representation in its ABI). The harness now passes
172 fixtures and 4 negative controls on AVR.

The general lesson: when the gate flags a Ct fixture on a target, the
right reflex is to inspect the disassembly and ask "is the offending
instruction in MY wrapper, or in the library?" — and ALWAYS check the
wrapper first. A wrapper-introduced branch is a harness bug; a
library-introduced branch is a real CT regression.

## CI integration

`.github/workflows/ct-verify.yml` defines a parallel matrix job over
the priority targets. Each row:

1. Sets up the pinned `rustc` toolchain + the appropriate target.
2. Caches cargo via `Swatinem/rust-cache`.
3. Runs `cargo run --release -p ct-driver -- --target <triple> --json-out
   target/ct-report/<triple>.json`.
4. Uploads the JSON report as an artifact.

The job is hard-fail. The existing `rust.yml` workflow remains
unchanged; CT-verify is a separate workflow file so the check name
distinguishes it in the PR review UI.

## Downstream consumer pattern

`modmath` / `rsa_heapless` / `ed25519_heapless` / `pqc` should
replicate this structure in their own repos:

1. Their own `ct-verify/ct-fixtures/` member with `#[no_mangle]
   pub extern "C"` symbols for their own CT primitives (Montgomery
   multiplication, field add, modexp inner loop, etc.). The
   `black_box` discipline applies identically — review-gate any
   fixture that bypasses the macros.
2. Their own `ct-verify/ct-driver/` — copy from `fixed-bigint`
   initially. Factor a shared utility crate once two or three
   consumers have copied it. Premature abstraction risk if extracted
   before.
3. Their own `.github/workflows/ct-verify.yml` matrix.
4. The same per-target mnemonic tables (`ct-driver/src/mnemonics.rs`)
   — these are architecture-level facts, share verbatim.
5. Their own negative-control fixtures of their own (a non-CT
   modular reduction, a value-leaking comparison) so the harness
   keeps self-testing.

Each crate owns its own PR gate.

## Future pillars (seams in place now)

- **Hardware DWT cycle counting**: `ct-fixtures/src/seam.rs` exposes
  no-op `ct_seam_begin/end()` symbols. A future `ct-fixtures-mcu/`
  companion will depend on `cortex-m`/`cortex-m-rt`, link the same
  fixtures, wrap each call with `DWT::CYCCNT` reads, and run on a
  self-hosted runner via `probe-rs run`. Fixture symbols are stable
  so no rewrite is needed.
- **`cargo-checkct`** (Ledger's `binsec` wrapper, symbolic-execution
  CT verifier): add `ct-verify/checkct/checkct.toml` listing the same
  symbols + secret-arg indices. Run as an optional CI job
  (`continue-on-error: true` initially since `binsec` timeouts can be
  flaky). Covers Thumb + RISC-V + x86_64.
- **`dudect-bencher`** (host statistical t-test): one host-only
  bench crate. Posts cycle-count distribution comparisons as PR
  comments. Useful as a regression smoke when upstream `subtle`
  updates.
- **`ctgrind` / Valgrind taint** (host x86): wrap each Cat-B
  `ct_checked_*` fixture with `crabgrind` to mark inputs as
  uninitialized + run under Valgrind. Catches secret-derived memory
  access patterns that asm-grep can't see.

Each pillar adds a strictly orthogonal failure mode.

## Files

| Path | Purpose |
|---|---|
| `ct-fixtures/Cargo.toml` | Staticlib crate manifest |
| `ct-fixtures/src/lib.rs` | Module tree, panic handler, `ct_fix_*` macros (`black_box` discipline) |
| `ct-fixtures/src/fixtures_cat_{a,b,c}.rs` | The ~170 positive fixtures |
| `ct-fixtures/src/fixtures_neg.rs` | The 4 negative controls (harness self-test) |
| `ct-fixtures/src/seam.rs` | Weak `ct_seam_begin/end` for future DWT companion |
| `ct-driver/Cargo.toml` | Driver manifest |
| `ct-driver/src/main.rs` | CLI, build orchestration, two-pass scan |
| `ct-driver/src/target.rs` | `TargetSpec` table in priority order |
| `ct-driver/src/mnemonics.rs` | Per-arch forbidden / allowed regex tables |
| `ct-driver/src/parse.rs` | objdump output → function blocks → violations, with Thumb IT-state machine |
| `ct-driver/src/report.rs` | JSON + human-readable report shape |
| `../.github/workflows/ct-verify.yml` | GitHub Actions matrix job |

## Coverage gaps surfaced by ct-ctgrind (2026-06)

The taint-tracking layer (ct-ctgrind, PR #119) caught its first real
bug within minutes of being wired up, and that bug already
exposes a structural gap in what we can verify per-architecture.

LLVM recognizes the textbook CT idiom

    target = if_zero ^ (mask & (if_zero ^ if_one))

as algebraically equivalent to a select, and on some targets rewrites
it into the conditional-move family — `cmov` on x86_64, `csel` on
aarch64, IT-block predicated execution on Thumb. The rewrite is
branch-free, so asm-grep is satisfied; the conditional-move's
*condition flag* comes from the secret, which is a cache-timing /
side-channel leak that runtime taint analysis (Valgrind/memcheck)
catches. That's exactly what the layered defense was set up to
expose, but it also tells us which architectures we currently lack
*any* check against this pattern.

Three of the priority targets have CT-friendly conditional-select
instructions whose mnemonics are on asm-grep's allowlist:

- **x86_64** — `cmovcc`, `setcc`, `sbb`. ctgrind covers this in CI today.
- **aarch64** — `csel`, `cset`, `csinc`, `ccmp`. ctgrind *could*
  cover this (`ubuntu-latest` aarch64 runners exist, Valgrind on
  aarch64-linux works), but the current workflow is x86_64-only.
  Worse, LLVM's aarch64 backend happens not to apply the rewrite to
  `const_leading_zeros_ct` / `const_trailing_zeros_ct` today —
  which gave the PR #118 fix a false-positive clean local run. We
  are trusting compiler heuristics we don't control.
- **thumbv7m / thumbv7em** — IT blocks. Any conditional instruction
  inside an active IT window is allowed by asm-grep, and we have no
  taint-tracking option on bare-metal. This is the deployment target
  for downstream Cortex-M crypto consumers (modmath, rsa_heapless,
  ed25519_heapless, pqc). We currently have zero visibility into
  whether the same select-rewrite is already shipping on the most
  important target.

The other priority targets are safer almost by accident: thumbv6m,
riscv32, and AVR have no conditional-select instruction at all.
Anything LLVM produces from a select pattern that needs runtime
data has to come out as a real branch — which asm-grep catches.

**Near-term mitigations available with current infrastructure:**

- Add an `aarch64-linux` matrix row to `.github/workflows/ct-ctgrind.yml`.
  Closes the aarch64 gap that PR #118's compiler-heuristic false
  positive exposed. ~5 lines.
- Default the local Docker workflow to `--platform linux/amd64` (or
  run both arches in sequence). Rosetta makes amd64 fast enough on
  Apple Silicon, and CI is x86_64-only anyway — matching that arch
  locally would have caught the PR #118 incompleteness before push.

**Larger mitigation, deferred until ctgrind lands:**

- cargo-checkct (Ledger's binsec wrapper) — symbolic execution on
  thumb + riscv32 + x86_64 binaries. Catches the select-rewrite
  family on the embedded targets where neither ctgrind nor any
  asm-grep allowlist tweak can reach. This is the natural Pillar 3
  per the original roadmap and would, combined with multi-arch
  ctgrind, give every priority target *at least one* tool that sees
  beyond raw branch mnemonics.

**The honest limit:** even all three layers won't be exhaustive. The
space of "secret-dependent observable behavior" is broader than any
single tool covers — cache timing on shared caches, secret-dependent
prefetch patterns, speculative execution side effects, microarchitec-
tural state that DWT cycle counts mask. The goal isn't a perfect
gate, it's enough orthogonal coverage that an attacker has to find a
class of bug that none of the layers see — and that we can audit the
gap consciously rather than by accident.

## Sources of the asymmetry, recorded for context

The PR #118 fix (`black_box` on `choice` in `const_ct_select`) was
correct in mechanism but incomplete in scope. The same XOR-based
select idiom is open-coded in:

- `const_shl_ct` / `const_shr_ct` inner loops (covered by PR #118)
- `const_leading_zeros_ct` (`total += (!decided) & v_lz`) — NOT covered
- `const_trailing_zeros_ct` — same pattern, NOT covered
- Likely others: any code path that masks-and-accumulates a
  secret-derived condition flag

A follow-up library PR needs to walk every Ct primitive and apply
the same `black_box` discipline anywhere a 0/all-ones mask gets
multiplied or ANDed with secret-derived state. The audit is a grep
for `mask`, `!decided`, `wrapping_neg` of a bit, and similar
constructions — small in scope, large in consequence.

## Track A investigation, follow-up notes (2026-06-02)

The audit above identified the four sites and the fix was applied
(`fix-ct-counting-zeros` branch, commit `0173383`): `black_box`
opacification on the `mask`/`!decided`/`wrapping_neg`-derived bit
in `const_leading_zeros_ct`, `const_trailing_zeros_ct`,
`const_cmp_ct`, and the `ct_checked_pow` inner loop. Library tests
still pass; the fixes are defensible by the same mechanism as #118.

But the x86_64 ctgrind failures *didn't clear*, and the underlying
cause is upstream:

**`u32::leading_zeros()` on baseline x86_64 (no `lzcnt`/BMI1)
compiles to**

```
test  reg, reg
je    .zero_handler   ; conditional jump on tainted ZF
bsr   reg, reg
xor   reg, 31
.zero_handler:
mov   reg, 32
```

The `je` exists because `bsr` is undefined-on-zero — LLVM emits a
zero-case branch around it. On a tainted limb, that's a real
data-dependent branch in the Rust standard library's intrinsic
lowering, no `black_box` placement in our code can defeat it.

**Which architectures are affected by this specific issue:**

- baseline x86_64 (no `lzcnt`): tripped — the `je` is real.
- x86_64-v2 and above: clean — `lzcnt` is unconditional, single
  instruction.
- aarch64: clean — `CLZ` is unconditional from the base ISA.
- Cortex-M3/M4/M7 (thumbv7m+): clean — `CLZ` is in v7m base.
- Cortex-M0 (thumbv6m): N/A in practice — `u32::leading_zeros()`
  lowers to a software polynomial that's branchless on most
  reasonable LLVM versions, but worth re-checking if we ever surface
  ctgrind coverage on this target.
- RISC-V with Zbb: clean — `clz` instruction.
- RISC-V without Zbb: needs verification — software lowering may or
  may not branch.
- AVR: definitely affected — no CLZ-like instruction, software
  lowering branches.

**Resolution path chosen (2026-06-02):**

1. ct-ctgrind's x86_64 workflow row gets `-C target-cpu=x86-64-v2`
   in a follow-up update (not in this PR — the workflow file is on
   the ct-ctgrind branch, not on main). Documents that the library
   assumes a CPU baseline with `lzcnt` / `popcnt` / etc., which is
   true for every x86_64 deployment from 2010 onwards.
2. The current PR (`fix-ct-counting-zeros`) lands the `black_box`
   opacification of the four mask-select sites. These are real
   defensive fixes for the same XOR-select pattern PR #118
   addressed, just at different sites. They don't clear x86_64
   ctgrind because the failing tests are tripping at a different
   place (`u32::leading_zeros()` intrinsic), but they prevent
   latent rewrites of our own select code at sites no fixture
   currently exposes.
3. **Follow-on PR (deferred):** tighten asm-grep's symbol scope so
   it also inspects helper-internal functions reachable from a
   fixture. This would catch the `je` inside `u32::leading_zeros`'s
   lowering on baseline x86_64 directly, at the asm-grep layer, on
   every priority target — much cheaper than waiting for ctgrind to
   trip it. The scope-trade-off in #117 was conscious but assumed
   helpers would be inlined under LTO; this finding shows that's not
   always true.

**The `subtle` style assumption.** subtle's `Choice::from(u8)`
applies `black_box` to opacify the input. Our `const_ct_select` and
the new fixes do the same on the mask-derived path. But neither
`subtle` nor our code protects against the case where the *primitive
intrinsics themselves* (leading_zeros, trailing_zeros, count_ones,
etc.) compile to branchful sequences on the underlying ISA. That's a
deployment-target concern, not a library implementation choice — at
least until someone writes a `ct-subtle` that re-implements every
primitive bit-op branchlessly from arithmetic. We're not there yet
and the cost/benefit doesn't justify being there yet for fixed-bigint.

## Remaining work after ct-ctgrind merges (2026-06-03)

Three concrete follow-ups remain on the verification stack. Ordered
by leverage, not by sequence — they're independent.

### 1. Tighten asm-grep's symbol scope to follow helpers

PR #117 deliberately scoped the asm-grep gate to `ct_fix__*` /
`nct_fix__*` symbols only, accepting the trade-off that helper
functions in `fixed_bigint::*` are inspected only to the extent that
LTO inlines them into the fixture body. PR #119's ctgrind finding
showed when this bites: `const_leading_zeros_ct` doesn't inline into
the fixture (it's a non-trivial helper), so when its `u32::leading_zeros()`
intrinsic call lowered to `test/je/bsr` on baseline x86_64, asm-grep
never saw the `je`. We worked around this by setting `+lzcnt,+bmi1`
in ctgrind's x86_64 workflow row — but only ctgrind catches this
class of issue today, and ctgrind only runs on x86_64 + aarch64.

Tightening the scope would catch the same class of bug on thumb,
RISC-V, and AVR — the targets where ctgrind can't reach. The work
is local to `ct-driver/src/parse.rs` and `ct-driver/src/main.rs`:
build a reachability set by walking call edges out of each
`ct_fix__*` symbol's disassembly, then include those helpers in the
scan. Need to be careful about false positives from
public-parameter loop bounds (the original reason for the scope
restriction) — likely needs a per-helper allowlist or a smarter
classifier for "loop counter compared to compile-time `N`" vs
"value compared to secret".

Estimated effort: medium. One focused PR in ct-driver.

### 2. cargo-checkct as Pillar 3

The whole reason for the layered model was that asm-grep + ctgrind
together still leave thumb (the actual Cortex-M deployment target
for downstream crypto consumers) with no taint/symbolic coverage.
cargo-checkct (Ledger's binsec wrapper) does symbolic execution on
binaries and supports thumb, RISC-V, and x86_64 — exactly the gap.
The setup is heavier than ctgrind: a `checkct.toml` config listing
each fixture symbol with which arguments are secret, plus a CI job
that runs binsec (with `continue-on-error: true` initially, because
binsec timeouts can be flaky).

Estimated effort: medium-high. Bigger PR but the right pillar to
add next. Particularly valuable if downstream consumers (modmath,
rsa_heapless, ed25519_heapless, pqc) replicate the pattern — they'd
get thumb coverage on their own primitives at the same cost.

### 3. Asymmetric-taint regression fixtures

CodeRabbit's nitpick from PR #120 review, deferred until ctgrind
landed (which it now has). The PR #118 / PR #120 `black_box`
opacification is load-bearing: if someone removes it later, the
LLVM XOR-select → cmov rewrite comes back. The current fixtures
don't catch this regression because they taint both operands
symmetrically — the rewrite to a secret-flag cmov only fires when
one operand is non-tainted (which is the asymmetric case `next_pow2`
exposed).

Add a small batch of fixtures targeting each load-bearing
`black_box` site (`const_ct_select`, `const_shl_ct` / `const_shr_ct`,
`const_leading_zeros_ct` / `const_trailing_zeros_ct`, `const_cmp_ct`,
`ct_checked_pow`) with asymmetric-taint setup: tainted secret +
non-tainted constant. If anyone removes the `black_box` in a future
refactor, these fixtures trip ctgrind immediately.

Estimated effort: small. One PR in ct-fixtures + ct-ctgrind.

### Why not add anything else here

`subtle`-style branchless re-implementations of the bit-counting
primitives is a real option but it's deployment-target driven — if
we ever want fixed-bigint to be CT on baseline x86_64 or AVR without
relying on a CPU-feature opt-in, that's the path. Right now neither
is a realistic deployment target for the downstream consumers, so
the cost-benefit doesn't justify it. Same answer for the hardware
DWT pillar — extremely high value if anyone ships fixed-bigint to a
specific Cortex-M target where cycle counts matter, but operational
cost (self-hosted runner + board) is too high without a concrete
consumer demanding it.
