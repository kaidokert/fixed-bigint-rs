//! Carrier-parity regression: `HeaplessBigInt<T, CAP>` must behave as a
//! fixed-`CAP`-width integer, matching `FixedUInt<T, CAP>` and being a
//! function of operand *values* only — never of how an operand's `len`
//! was carried.
//!
//! Grew out of a Montgomery-multiply divergence hunt: the carrier bug
//! that surfaced was subtraction wrapping at `max(operand_len)` instead
//! of `CAP`, making `wrapping_sub` representation-dependent. These tests
//! lock the fixed-width, value-deterministic contract for every op a
//! modular-arithmetic consumer leans on.

#![cfg(all(feature = "heapless-runtime-len", feature = "num-traits"))]

use const_num_traits::{CheckedMul, Nct, OverflowingAdd, OverflowingSub};
use core::ops::RemAssign;
use fixed_bigint::{FixedUInt, HeaplessBigInt};

type H = HeaplessBigInt<u8, 4, Nct>;
type F = FixedUInt<u8, 4>;

fn h_val(v: &H) -> u64 {
    let mut buf = [0u8; 4];
    let s = v.to_le_bytes(&mut buf);
    let mut acc = 0u64;
    for (i, b) in s.iter().enumerate() {
        acc |= (*b as u64) << (8 * i);
    }
    acc
}

fn f_val(v: &F) -> u64 {
    use num_traits::ToPrimitive;
    v.to_u64().unwrap()
}

// Same value, chosen len (zero-tail invariant holds for both).
fn h(val: u8, len: u16) -> H {
    H::from_limbs([val, 0, 0, 0], len)
}

#[test]
fn ops_are_len_invariant() {
    // op(value @ len 1) must equal op(value @ len 2/4) in VALUE.
    for val in [0u8, 1, 5, 8, 11, 13, 16, 100, 200, 255] {
        for sh in [0usize, 1, 3, 4, 7, 8, 9] {
            let s = [
                h_val(&(h(val, 1) << sh)),
                h_val(&(h(val, 2) << sh)),
                h_val(&(h(val, 4) << sh)),
            ];
            assert_eq!(s[0], s[1], "Shl val={val} sh={sh}");
            assert_eq!(s[0], s[2], "Shl val={val} sh={sh}");
            let r1 = h_val(&(h(val, 1) >> sh));
            let r4 = h_val(&(h(val, 4) >> sh));
            assert_eq!(r1, r4, "Shr val={val} sh={sh}");
        }
    }
    for a in [0u8, 5, 8, 15, 100, 200, 255] {
        for mask in [1u8, 15, 0xFF] {
            let mut vals = [0u64; 9];
            let mut k = 0;
            for al in [1u16, 2, 4] {
                for ml in [1u16, 2, 4] {
                    vals[k] = h_val(&(&h(a, al) & &h(mask, ml)));
                    k += 1;
                }
            }
            for w in vals.windows(2) {
                assert_eq!(w[0], w[1], "BitAnd a={a} mask={mask}");
            }
        }
    }
}

#[test]
fn per_op_matches_fixeduint() {
    // Every op's result (value + flag) matches FixedUInt<u8,4>, over
    // operands carried at len 1, 2, and 4.
    let ff = |v: u8| F::from(v as u32);
    for a in [0u8, 1, 5, 7, 8, 11, 12] {
        for b in [1u8, 5, 7, 11, 13] {
            for al in [1u16, 2, 4] {
                let (hs, ho) = OverflowingAdd::overflowing_add(h(a, al), h(b, al));
                let (fs, fo) = OverflowingAdd::overflowing_add(ff(a), ff(b));
                assert_eq!((h_val(&hs), ho), (f_val(&fs), fo), "add {a}+{b} al={al}");

                let (hd, hb) = OverflowingSub::overflowing_sub(h(a, al), h(b, al));
                let (fd, fb) = OverflowingSub::overflowing_sub(ff(a), ff(b));
                assert_eq!((h_val(&hd), hb), (f_val(&fd), fb), "sub {a}-{b} al={al}");

                let hm = CheckedMul::checked_mul(h(a, al), h(b, al)).map(|x| h_val(&x));
                let fm = CheckedMul::checked_mul(ff(a), ff(b)).map(|x| f_val(&x));
                assert_eq!(hm, fm, "mul {a}*{b} al={al}");

                assert_eq!(
                    h_val(&(&h(a, al) % &h(b, al))),
                    f_val(&(&ff(a) % &ff(b))),
                    "rem {a}%{b} al={al}"
                );

                let mut hra = h(a, al);
                hra.rem_assign(&h(b, al));
                let mut fra = ff(a);
                fra %= ff(b);
                assert_eq!(h_val(&hra), f_val(&fra), "rem_assign {a}%{b} al={al}");

                assert_eq!(
                    h(a, al).partial_cmp(&h(b, al)),
                    ff(a).partial_cmp(&ff(b)),
                    "cmp {a}?{b} al={al}"
                );
            }
        }
    }
}
