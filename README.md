# Fixed BigInt

[![crate](https://img.shields.io/crates/v/fixed-bigint.svg)](https://crates.io/crates/fixed-bigint)
[![documentation](https://docs.rs/fixed-bigint/badge.svg)](https://docs.rs/fixed-bigint/)
[![minimum rustc 1.51](https://img.shields.io/badge/rustc-1.51+-red.svg)](https://rust-lang.github.io/rfcs/2495-min-rust-version.html)
[![build status](https://github.com/kaidokert/fixed-bigint-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/kaidokert/fixed-bigint-rs/actions)
[![Coverage Status](https://coveralls.io/repos/github/kaidokert/fixed-bigint-rs/badge.svg?branch=main)](https://coveralls.io/github/kaidokert/fixed-bigint-rs?branch=main)

Unsigned BigInt implementation, backed by a fixed-size array.

***Important***: Requires at least Rust 1.51 stable, as it uses `min_const_generics`

`FixedUInt<u8,4>`,`FixedUInt<u16,2>` or `FixedUInt<u32,1>` all create a 32-bit unsigned integer, that behaves mostly the same as builtin `u32`.
`FixedUInt<u32, 64>` creates a 2048-bit value, that uses native 32-bit math. If running on 8-bit CPU, `FixedUInt<u8, 2048>` would work the same, just very much slower.

The crate is written for `no_std` and `no_alloc` environments with option for panic-free operation, i.e. embedded MCUs. At least for now, focus is on correctness first and then generated code size, performance comes last. The aim is not to bring in 64-bit math dependencies on 32-bit CPU, to save code space.

The arithmetic operands ( +, -, .add() ) panic on overflow, just like native integer types. Panic-free alternatives like `overlowing_add` and `wrapping_add` are supported.

In addition to basic arithmetic, two main traits are implemented: [num_traits::PrimInt](https://docs.rs/num-traits/latest/num_traits/int/trait.PrimInt.html) and [num_integer::Integer](https://docs.rs/num/latest/num/integer/trait.Integer.html).

_TODO list_:
 * Implement experimental `unchecked_math` operands, unchecked_mul, unchecked_div etc.
 * Probably needs its own error structs instead of reusing core::fmt::Error and core::num::ParseIntError
 * Maybe implement signed version as well.
 * Adopt `const_trait` from nightly and constify everything

_Note:_ This crate is mostly written as an exercise for learning the Rust type system and understanding how well it works on microcontrollers, its fitness for any particular purpose or quality has precisely zero guarantees.

If you are looking for production quality implementation with `no_std`, fixed-size bigint, suitable for crypto, please check out [crypto-bigint](https://github.com/RustCrypto/crypto-bigint) or [bnum](https://crates.io/crates/bnum) crate.

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
