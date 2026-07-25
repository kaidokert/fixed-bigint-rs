#![no_main]
#![no_std]

use const_num_traits::{Ct, Nct};
use core::hint::black_box;
use cortex_m_rt::entry;
// Every measured op body comes from the shared workload catalog — the same
// definitions the emulated (asm-grep / ctgrind) backends drive. This file only
// constructs inputs, calls the catalog op, and consumes the result.
use ct_workload as catalog;
use fixed_bigint::FixedUInt;
use krabi_caliper::cortex_m::DwtMeasurementPlatform;
use krabi_caliper::report::Field;
use krabi_caliper::suite::{PairedSuite, PairedSuiteConfig, PairedSuiteFields};

const TRIALS: usize = 4;
const BATCHES: usize = 16;
const MAX_POSITIVE_SPREAD: u32 = 32;

const _: () = assert!(
    cfg!(feature = "carrier-u32x8") as usize
        + cfg!(feature = "carrier-u32x16") as usize
        + cfg!(feature = "carrier-u8x32") as usize
        == 1,
    "enable exactly one carrier feature",
);

#[cfg(feature = "carrier-u32x8")]
type Word = u32;
#[cfg(feature = "carrier-u32x8")]
const N: usize = 8;
#[cfg(feature = "carrier-u32x8")]
const CARRIER: &str = "u32x8";

#[cfg(feature = "carrier-u32x16")]
type Word = u32;
#[cfg(feature = "carrier-u32x16")]
const N: usize = 16;
#[cfg(feature = "carrier-u32x16")]
const CARRIER: &str = "u32x16";

#[cfg(feature = "carrier-u8x32")]
type Word = u8;
#[cfg(feature = "carrier-u8x32")]
const N: usize = 32;
#[cfg(feature = "carrier-u8x32")]
const CARRIER: &str = "u8x32";

type Words = [Word; N];
type CtUInt = FixedUInt<Word, N, Ct>;
type NctUInt = FixedUInt<Word, N, Nct>;

// The `is_some().unwrap_u8()` / `unwrap_or(zero)` split of a checked op's
// `CtOption` is the measurement harness's concern (write value, keep validity),
// so it stays here; the op itself is `catalog::ct_checked_*`.
#[inline(never)]
fn fixture_ct_eq(a: &Words, b: &Words) -> bool {
    let x = CtUInt::from(black_box(*a));
    let y = CtUInt::from(black_box(*b));
    let _ = black_box(catalog::ct_eq(x, y));
    true
}

#[inline(never)]
fn fixture_conditional_select(choice: u8) -> bool {
    let zero = CtUInt::from([0; N]);
    let mut one_words = [0; N];
    one_words[0] = 1;
    let one = CtUInt::from(one_words);
    let selected = catalog::cond_select(zero, one, black_box(choice));
    let _ = black_box(*selected.words());
    true
}

#[inline(never)]
fn fixture_checked_add(a: &Words, b: &Words) -> bool {
    let result = catalog::ct_checked_add(CtUInt::from(black_box(*a)), CtUInt::from(black_box(*b)));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_checked_mul(a: &Words, b: &Words) -> bool {
    let result = catalog::ct_checked_mul(CtUInt::from(black_box(*a)), CtUInt::from(black_box(*b)));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_checked_shl(a: &Words, amount: u32) -> bool {
    let result = catalog::ct_checked_shl(CtUInt::from(black_box(*a)), black_box(amount));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_checked_pow(exp: u32) -> bool {
    let mut base_words = [0; N];
    base_words[0] = 2;
    let result = catalog::ct_checked_pow(CtUInt::from(base_words), black_box(exp));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_is_zero(a: &Words) -> bool {
    let _ = black_box(catalog::is_zero(CtUInt::from(black_box(*a))));
    true
}

#[inline(never)]
fn fixture_nct_div(a: &Words, b: &Words) -> bool {
    let value = catalog::nct_div(NctUInt::from(black_box(*a)), NctUInt::from(black_box(*b)));
    let _ = black_box(*value.words());
    true
}

#[inline(never)]
fn fixture_nct_ilog10(a: &Words) -> bool {
    let _ = black_box(catalog::nct_ilog10(NctUInt::from(black_box(*a))));
    true
}

// ── hardware-regressions tier: the paths where leaks were found or nearly
// found. A/B pairs are chosen so a non-CT implementation would separate in
// cycles (small vs large shift amount, minimal vs maximal carry propagation,
// no-overflow vs overflow in the cios shift row). All use the shared catalog.

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_shl_usize(a: &Words, amount: usize) -> bool {
    let r = catalog::shl_usize(CtUInt::from(black_box(*a)), black_box(amount));
    let _ = black_box(*r.words());
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_carrying_mul(a: &Words, b: &Words, carry: &Words) -> bool {
    let (lo, hi) = catalog::carrying_mul(
        CtUInt::from(black_box(*a)),
        CtUInt::from(black_box(*b)),
        CtUInt::from(black_box(*carry)),
    );
    let _ = black_box((*lo.words(), *hi.words()));
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_cios_shift(mult: &Words, acc: &Words, scalar: Word, acc_hi: Word) -> bool {
    let (acc2, cout) = catalog::cios_mul_acc_shift_row(
        black_box(scalar),
        CtUInt::from(black_box(*mult)),
        CtUInt::from(black_box(*acc)),
        black_box(acc_hi),
    );
    let _ = black_box((*acc2.words(), cout));
    true
}

// HeaplessBigInt — the carrier the smoke tier never touches. Held full-width
// (`len == N`) so it matches `FixedUInt<Word, N>`.
#[cfg(feature = "hardware-regressions")]
type HUInt = fixed_bigint::HeaplessBigInt<Word, N, Ct>;

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_h_sat_add(a: &Words, b: &Words) -> bool {
    let x = HUInt::from_limbs(black_box(*a), N as u16);
    let y = HUInt::from_limbs(black_box(*b), N as u16);
    let _ = black_box(*catalog::sat_add(x, y).all_limbs());
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_h_shl_usize(a: &Words, amount: usize) -> bool {
    let x = HUInt::from_limbs(black_box(*a), N as u16);
    let _ = black_box(*catalog::shl_usize(x, black_box(amount)).all_limbs());
    true
}

// ── modmath secret-path primitives: the CT ops the live crypto stack runs on
// secret residues/exponents but which the smoke tier never measures. RSA's
// blinded modexp drives ct_lt/ct_is_zero/ct_is_odd (CIOS reduce + safegcd_ct
// inverse), borrowing_sub (CIOS final conditional −modulus), and cios_mul_acc_row
// (the non-shift CIOS row, run every Montgomery multiply); ed25519's FieldCt
// add/sub drives wrapping_add/wrapping_sub/overflowing_add on secret scalars.
// A/B pairs flip the branch a non-CT impl would take (zero↔dense, even↔odd,
// minimal↔maximal borrow/carry propagation).

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_ct_lt(a: &Words, b: &Words) -> bool {
    let _ = black_box(catalog::ct_lt(
        CtUInt::from(black_box(*a)),
        CtUInt::from(black_box(*b)),
    ));
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_ct_is_zero(a: &Words) -> bool {
    let _ = black_box(catalog::ct_is_zero(CtUInt::from(black_box(*a))));
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_ct_is_odd(a: &Words) -> bool {
    let _ = black_box(catalog::ct_is_odd(CtUInt::from(black_box(*a))));
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_borrowing_sub(a: &Words, b: &Words, borrow: bool) -> bool {
    let (diff, bout) = catalog::borrowing_sub(
        CtUInt::from(black_box(*a)),
        CtUInt::from(black_box(*b)),
        black_box(borrow),
    );
    let _ = black_box((*diff.words(), bout));
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_cios_row(mult: &Words, acc: &Words, scalar: Word, carry: Word) -> bool {
    let (acc2, cout) = catalog::cios_mul_acc_row(
        black_box(scalar),
        CtUInt::from(black_box(*mult)),
        CtUInt::from(black_box(*acc)),
        black_box(carry),
    );
    let _ = black_box((*acc2.words(), cout));
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_wrapping_add(a: &Words, b: &Words) -> bool {
    let r = catalog::wrapping_add(CtUInt::from(black_box(*a)), CtUInt::from(black_box(*b)));
    let _ = black_box(*r.words());
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_wrapping_sub(a: &Words, b: &Words) -> bool {
    let r = catalog::wrapping_sub(CtUInt::from(black_box(*a)), CtUInt::from(black_box(*b)));
    let _ = black_box(*r.words());
    true
}

#[cfg(feature = "hardware-regressions")]
#[inline(never)]
fn fixture_overflowing_add(a: &Words, b: &Words) -> bool {
    let r = catalog::overflowing_add(CtUInt::from(black_box(*a)), CtUInt::from(black_box(*b)));
    let _ = black_box(*r.words());
    true
}

#[entry]
fn main() -> ! {
    let mut reporter = krabi_caliper::protocol::rtt::init_ct_compatible();
    let mut peripherals = cortex_m::Peripherals::take().unwrap();
    let mut counter = DwtMeasurementPlatform::enable(
        &mut peripherals.DCB,
        &mut peripherals.DWT,
        Some(16_000_000),
    )
    .unwrap();

    let zero = [0; N];
    let mut sparse = [0; N];
    sparse[0] = 3;
    sparse[N - 1] = 1;
    let mut dense = [Word::MAX; N];
    dense[0] = Word::MAX - 2;
    let mut one = [0; N];
    one[0] = 1;
    let mut divisor = [0; N];
    divisor[0] = 3;
    let mut small_decimal = [0; N];
    small_decimal[0] = 9;
    let mut large_decimal = [0; N];
    large_decimal[0] = Word::MAX;
    large_decimal[1] = Word::MAX;

    let run_fields = [
        Field::token("carrier", CARRIER),
        Field::u64("trials", TRIALS as u64),
        Field::u64("batches", BATCHES as u64),
        Field::u64("max_positive_spread", MAX_POSITIVE_SPREAD as u64),
    ];
    let fixture_fields = [
        Field::token("carrier", CARRIER),
        Field::u64("batches", BATCHES as u64),
    ];
    let summary_fields = [Field::token("carrier", CARRIER)];
    let mut suite = PairedSuite::<_, _, TRIALS>::start(
        &mut counter,
        &mut reporter,
        PairedSuiteConfig {
            suite: "fixed-bigint-cyccnt",
            target: "thumbv7em-none-eabihf",
            board: Some("stm32f407vg"),
            unit: krabi_caliper::Unit::CoreCycles,
            frequency_hz: Some(16_000_000),
            warmup_blocks: 2,
            batches: BATCHES,
            positive_max_spread: MAX_POSITIVE_SPREAD as u64,
            positive_require_overlap: false,
            fields: PairedSuiteFields {
                run: &run_fields,
                fixture: &fixture_fields,
                summary: &summary_fields,
            },
        },
    )
    .unwrap();
    suite
        .positive("ct_eq", &(&zero, &zero), &(&sparse, &dense), |&(a, b)| {
            fixture_ct_eq(a, b)
        })
        .unwrap();
    suite
        .positive("conditional_select", &0, &1, |&choice| {
            fixture_conditional_select(choice)
        })
        .unwrap();
    suite
        .positive(
            "ct_checked_add",
            &(&one, &sparse),
            &(&dense, &one),
            |&(a, b)| fixture_checked_add(a, b),
        )
        .unwrap();
    suite
        .positive(
            "ct_checked_mul",
            &(&one, &sparse),
            &(&dense, &dense),
            |&(a, b)| fixture_checked_mul(a, b),
        )
        .unwrap();
    suite
        .positive(
            "ct_checked_shl",
            &(&sparse, 1),
            &(&sparse, (N as u32 * Word::BITS) - 1),
            |&(a, amount)| fixture_checked_shl(a, amount),
        )
        .unwrap();
    suite
        .positive("ct_checked_pow", &3, &29, |&exp| fixture_checked_pow(exp))
        .unwrap();
    suite
        .positive("is_zero", &zero, &dense, fixture_is_zero)
        .unwrap();
    suite
        .negative(
            "nct_div",
            &(&one, &divisor),
            &(&dense, &divisor),
            |&(a, b)| fixture_nct_div(a, b),
        )
        .unwrap();
    suite
        .negative(
            "nct_ilog10",
            &small_decimal,
            &large_decimal,
            fixture_nct_ilog10,
        )
        .unwrap();

    #[cfg(feature = "hardware-regressions")]
    {
        let max_shift = (N * Word::BITS as usize) - 1;
        suite
            .positive(
                "shl_usize",
                &(&sparse, 1usize),
                &(&sparse, max_shift),
                |&(a, amount)| fixture_shl_usize(a, amount),
            )
            .unwrap();
        suite
            .positive(
                "carrying_mul",
                &(&zero, &zero, &zero),
                &(&dense, &dense, &dense),
                |&(a, b, c)| fixture_carrying_mul(a, b, c),
            )
            .unwrap();
        suite
            .positive(
                "cios_mul_acc_shift_row",
                &(&sparse, &zero, 3 as Word, 0 as Word),
                &(&dense, &dense, Word::MAX, Word::MAX),
                |&(m, a, s, h)| fixture_cios_shift(m, a, s, h),
            )
            .unwrap();
        suite
            .positive(
                "h_sat_add",
                &(&zero, &zero),
                &(&sparse, &dense),
                |&(a, b)| fixture_h_sat_add(a, b),
            )
            .unwrap();
        suite
            .positive(
                "h_shl_usize",
                &(&sparse, 1usize),
                &(&sparse, max_shift),
                |&(a, amount)| fixture_h_shl_usize(a, amount),
            )
            .unwrap();

        // modmath secret-path primitives (see fixture comment above).
        suite
            .positive("ct_lt", &(&zero, &dense), &(&dense, &zero), |&(a, b)| {
                fixture_ct_lt(a, b)
            })
            .unwrap();
        suite
            .positive("ct_is_zero", &zero, &dense, fixture_ct_is_zero)
            .unwrap();
        suite
            .positive("ct_is_odd", &zero, &one, fixture_ct_is_odd)
            .unwrap();
        suite
            .positive(
                "borrowing_sub",
                &(&zero, &zero, false),
                &(&dense, &dense, true),
                |&(a, b, borrow)| fixture_borrowing_sub(a, b, borrow),
            )
            .unwrap();
        suite
            .positive(
                "cios_mul_acc_row",
                &(&sparse, &zero, 3 as Word, 0 as Word),
                &(&dense, &dense, Word::MAX, Word::MAX),
                |&(m, a, s, c)| fixture_cios_row(m, a, s, c),
            )
            .unwrap();
        suite
            .positive(
                "wrapping_add",
                &(&zero, &zero),
                &(&dense, &dense),
                |&(a, b)| fixture_wrapping_add(a, b),
            )
            .unwrap();
        suite
            .positive(
                "wrapping_sub",
                &(&dense, &zero),
                &(&zero, &dense),
                |&(a, b)| fixture_wrapping_sub(a, b),
            )
            .unwrap();
        suite
            .positive(
                "overflowing_add",
                &(&zero, &zero),
                &(&dense, &dense),
                |&(a, b)| fixture_overflowing_add(a, b),
            )
            .unwrap();
    }

    suite.finish().unwrap();
    loop {
        cortex_m::asm::nop();
    }
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    krabi_caliper::protocol::rtt::print(format_args!("PANIC: {}\n", info));
    loop {
        cortex_m::asm::nop();
    }
}
