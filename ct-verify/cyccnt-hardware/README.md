# fixed-bigint CYCCNT fixtures

Runs a curated set of `fixed-bigint` constant-time primitives on the J-Trace
STM32F407VG. Each recorded sample batches 16 calls, executes with interrupts
masked, and is collected in balanced ABBA order. The Nct division and ilog10
fixtures are negative controls and must have disjoint A/B timing ranges.
Positive fixtures have an absolute 32-cycle combined-spread limit per batch,
equivalent to at most two cycles per primitive call. Unlike the much longer
Ed25519 operations, literal A/B range overlap is not required for these stable
batched microbenchmarks; all raw bounds remain visible for review.

Run the complete three-carrier hardware gate from this directory with the
shared Rust campaign runner:

```sh
cargo krabi-caliper run fixed-bigint-jtrace-f407
```

The declarative profile in `krabi-caliper.toml` owns release builds,
explicit SWD/J-Trace selection, RTT completion, deadlines, ELF retention,
raw logs, and JSON/Markdown results below
`target/krabi-caliper/fixed-bigint-jtrace-f407/`. To troubleshoot outside
the campaign runner, the equivalent direct Cargo commands remain:

```sh
cargo run --release --features carrier-u32x8
cargo run --release --features carrier-u32x16
cargo run --release --features carrier-u8x32
```

RTT output uses `krabi-caliper` schema version 1. It emits an `EM_BEGIN`
record with qualified target and 16 MHz counter metadata, every individual A/B
sample as `EM_SAMPLE`, each policy decision as `EM_RESULT`, and a final
`EM_SUMMARY`. During migration it also mirrors the existing `CT_BEGIN`,
`CT_RESULT`, and `CT_SUMMARY` records. The reporter uses a blocking RTT channel
so machine evidence cannot be silently truncated.

This is a timing-regression layer, not a replacement for ctgrind or the
cross-target conditional-branch audit.

Initial STM32F407/J-Trace calibration passed all nine fixtures on every
carrier. Positive combined spreads were 0–12 cycles per batch; the Nct
controls separated by approximately 1.74–14.6 million cycles per batch.
