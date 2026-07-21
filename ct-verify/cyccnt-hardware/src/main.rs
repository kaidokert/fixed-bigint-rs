#![no_main]
#![no_std]

use const_num_traits::{Ct, Ilog10, Nct, Zero};
use core::hint::black_box;
use cortex_m_rt::entry;
use fixed_bigint::FixedUInt;
use krabi_caliper::cortex_m::DwtMeasurementPlatform;
use krabi_caliper::report::Field;
use krabi_caliper::suite::{PairedSuite, PairedSuiteConfig, PairedSuiteFields};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

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

#[inline(never)]
fn fixture_ct_eq(a: &Words, b: &Words) -> bool {
    let x = CtUInt::from(black_box(*a));
    let y = CtUInt::from(black_box(*b));
    let _ = black_box(x.ct_eq(&y).unwrap_u8());
    true
}

#[inline(never)]
fn fixture_conditional_select(choice: u8) -> bool {
    let zero = CtUInt::from([0; N]);
    let mut one_words = [0; N];
    one_words[0] = 1;
    let one = CtUInt::from(one_words);
    let selected = CtUInt::conditional_select(&zero, &one, Choice::from(black_box(choice)));
    let _ = black_box(*selected.words());
    true
}

#[inline(never)]
fn fixture_checked_add(a: &Words, b: &Words) -> bool {
    let result = CtUInt::from(black_box(*a)).ct_checked_add(&CtUInt::from(black_box(*b)));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_checked_mul(a: &Words, b: &Words) -> bool {
    let result = CtUInt::from(black_box(*a)).ct_checked_mul(&CtUInt::from(black_box(*b)));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_checked_shl(a: &Words, amount: u32) -> bool {
    let result = CtUInt::from(black_box(*a)).ct_checked_shl(black_box(amount));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_checked_pow(exp: u32) -> bool {
    let mut base_words = [0; N];
    base_words[0] = 2;
    let result = CtUInt::from(base_words).ct_checked_pow(black_box(exp));
    let valid = result.is_some().unwrap_u8();
    let value = result.unwrap_or(CtUInt::from([0; N]));
    let _ = black_box((*value.words(), valid));
    true
}

#[inline(never)]
fn fixture_is_zero(a: &Words) -> bool {
    let value = CtUInt::from(black_box(*a));
    let _ = black_box(<CtUInt as Zero>::is_zero(&value));
    true
}

#[inline(never)]
fn fixture_nct_div(a: &Words, b: &Words) -> bool {
    let value = NctUInt::from(black_box(*a)) / NctUInt::from(black_box(*b));
    let _ = black_box(*value.words());
    true
}

#[inline(never)]
fn fixture_nct_ilog10(a: &Words) -> bool {
    let value = NctUInt::from(black_box(*a));
    let _ = black_box(Ilog10::ilog10(value));
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
