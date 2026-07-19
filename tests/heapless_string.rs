//! Heapless string surface at widths the fixed-width carrier harness can't
//! reach: sub-capacity values (a narrow value in a wide carrier) and
//! multi-limb rendering / parsing.

use fixed_bigint::HeaplessBigInt;

type H = HeaplessBigInt<u32, 8>; // 256-bit CAP

#[test]
fn display_hex_value_width() {
    // A small value in a wide carrier prints its value, never CAP-padded.
    assert_eq!(std::format!("{}", H::from(255u8)), "255");
    assert_eq!(std::format!("{:x}", H::from(255u8)), "ff");
    assert_eq!(std::format!("{:X}", H::from(255u8)), "FF");
    assert_eq!(std::format!("{}", H::from(0u8)), "0");

    // Multi-limb value: 2 u32 limbs (0xFEEDF00D_DEADBEEF), hex is MSB-first
    // over the value width with leading-zero suppression.
    let v = H::from_le_bytes(&[0xEF, 0xBE, 0xAD, 0xDE, 0x0D, 0xF0, 0xED, 0xFE]);
    assert_eq!(std::format!("{:x}", v), "feedf00ddeadbeef");
}

#[cfg(feature = "num-traits")]
#[test]
fn from_str_wide_roundtrip() {
    use core::str::FromStr;

    // A value wider than 32 bits parses into the wide carrier (the parse
    // accumulates at CAP width) and round-trips through Display.
    let v = H::from_le_bytes(&[0xEF, 0xBE, 0xAD, 0xDE, 0x0D, 0xF0, 0xED, 0xFE]);
    let dec = std::format!("{}", v);
    let back = H::from_str(&dec).unwrap();
    assert_eq!(std::format!("{}", back), dec);
    assert_eq!(std::format!("{:x}", back), "feedf00ddeadbeef");

    // Radix-16 parse agrees.
    let h = <H as num_traits::Num>::from_str_radix("feedf00ddeadbeef", 16).unwrap();
    assert_eq!(std::format!("{}", h), dec);

    assert!(H::from_str("").is_err());
    assert!(H::from_str("12x").is_err());
}
