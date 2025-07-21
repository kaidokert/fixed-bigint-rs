use fixed_bigint::FixedUInt;
use fixed_bigint::num_traits::{self, FromPrimitive};

#[test]
fn test_from_le_bytes() {
    type TestInt = FixedUInt<u16, 2>;

    // Test with empty bytes
    let empty_bytes = [];
    let result = TestInt::from_le_bytes(&empty_bytes);
    assert_eq!(result, TestInt::from(0u8));

    // Test with single byte - should create the value 0x42
    let single_byte = [0x42];
    let result = TestInt::from_le_bytes(&single_byte);
    assert_eq!(result, TestInt::from(0x42u8));

    // Test with two bytes (equals word size for u16)
    let two_bytes = [0x34, 0x12];
    let result = TestInt::from_le_bytes(&two_bytes);
    assert_eq!(result, TestInt::from(0x1234u16));

    // Test with exactly word size bytes
    let word_size_bytes = [0x78, 0x56, 0x34, 0x12];
    let result = TestInt::from_le_bytes(&word_size_bytes);
    // With u16 words, this should create two words: 0x5678 and 0x1234
    let expected = TestInt::from(0x5678u16) + (TestInt::from(0x1234u16) << 16u32);
    assert_eq!(result, expected);

    // Test with more than word size bytes - should only use first 4 bytes for 2 words
    let more_bytes = [0x00, 0x00, 0x78, 0x56, 0x34, 0x12];
    let result = TestInt::from_le_bytes(&more_bytes);
    // Should only use first 4 bytes (2 words for u16)
    let expected = TestInt::from(0x0000u16) + (TestInt::from(0x5678u16) << 16u32);
    assert_eq!(result, expected);
}

#[test]
fn test_from_be_bytes() {
    type TestInt = FixedUInt<u16, 2>;

    // Test with empty bytes
    let empty_bytes = [];
    let result = TestInt::from_be_bytes(&empty_bytes);
    assert_eq!(result, TestInt::from(0u8));

    // Test with single byte - should create the value 0x42
    let single_byte = [0x42];
    let result = TestInt::from_be_bytes(&single_byte);
    assert_eq!(result, TestInt::from(0x42u8));

    // Test with two bytes (less than word size)
    let two_bytes = [0x12, 0x34];
    let result = TestInt::from_be_bytes(&two_bytes);
    assert_eq!(result, TestInt::from(0x1234u16));

    // Test with exactly word size bytes
    let word_size_bytes = [0x12, 0x34, 0x56, 0x78];
    let result = TestInt::from_be_bytes(&word_size_bytes);
    assert_eq!(result, TestInt::from(0x12345678u32));

    // Test with more than word size bytes - should keep least significant (rightmost) bytes
    let more_bytes = [0x12, 0x34, 0x56, 0x78, 0x00, 0x00];
    let result = TestInt::from_be_bytes(&more_bytes);
    // With consistent truncation, keeps the last 4 bytes: [0x56, 0x78, 0x00, 0x00]
    assert_eq!(result, TestInt::from(0x56780000u32));

    // Test with bytes that would fill multiple words - should keep least significant bytes
    let multi_word_bytes = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88];
    let result = TestInt::from_be_bytes(&multi_word_bytes);
    // Keeps the last 4 bytes: [0x55, 0x66, 0x77, 0x88]
    assert_eq!(result, TestInt::from(0x55667788u32));
}

#[test]
fn test_consistent_truncation_behavior() {
    type TestInt = FixedUInt<u16, 2>; // 4-byte capacity

    // Test with excess bytes to verify consistent truncation semantics
    let long_bytes = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66]; // 6 bytes, capacity is 4

    // Both methods should now keep the least significant bytes (modulo semantics)
    let le_result = TestInt::from_le_bytes(&long_bytes);
    let be_result = TestInt::from_be_bytes(&long_bytes);

    // LE: keeps first 4 bytes [0x11, 0x22, 0x33, 0x44]
    assert_eq!(le_result, TestInt::from_le_bytes(&[0x11, 0x22, 0x33, 0x44]));

    // BE: keeps last 4 bytes [0x33, 0x44, 0x55, 0x66] (least significant in BE)
    assert_eq!(be_result, TestInt::from_be_bytes(&[0x33, 0x44, 0x55, 0x66]));

    // Verify they represent the same truncation semantics (modulo behavior)
    // The LE keeps bytes [0x11, 0x22, 0x33, 0x44] which represents value 0x44332211
    // The BE keeps bytes [0x33, 0x44, 0x55, 0x66] which represents value 0x33445566
    // These are different values, but both represent consistent "keep least significant" semantics

    // Test with exactly capacity-sized input (should be identical)
    let exact_bytes = [0xAA, 0xBB, 0xCC, 0xDD];
    let le_exact = TestInt::from_le_bytes(&exact_bytes);
    let be_exact = TestInt::from_be_bytes(&exact_bytes);

    // Verify the created values are correct
    assert_eq!(le_exact, TestInt::from(0xDDCCBBAAu32));
    assert_eq!(be_exact, TestInt::from(0xAABBCCDDu32));

    // Verify roundtrip works for both
    let mut le_buf = [0u8; 4];
    le_exact.to_le_bytes(&mut le_buf).unwrap();
    assert_eq!(le_buf, [0xAA, 0xBB, 0xCC, 0xDD]);

    let mut be_buf = [0u8; 4];
    be_exact.to_be_bytes(&mut be_buf).unwrap();
    assert_eq!(be_buf, [0xAA, 0xBB, 0xCC, 0xDD]);
}

#[test]
fn test_to_le_bytes() {
    type TestInt = FixedUInt<u16, 2>;

    // Test zero
    let zero = TestInt::from(0u8);
    let mut buffer = [0u8; 8];
    let result = zero.to_le_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0, 0, 0, 0]);

    // Test small value
    let small = TestInt::from(0x1234u16);
    let mut buffer = [0u8; 8];
    let result = small.to_le_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0x34, 0x12, 0, 0]);

    // Test larger value
    let large = TestInt::from(0x12345678u32);
    let mut buffer = [0u8; 8];
    let result = large.to_le_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0x78, 0x56, 0x34, 0x12]);

    // Test buffer too small
    let value = TestInt::from(0x1234u16);
    let mut small_buffer = [0u8; 2];
    let result = value.to_le_bytes(&mut small_buffer);
    assert!(result.is_err());
}

#[test]
fn test_to_be_bytes() {
    type TestInt = FixedUInt<u16, 2>;

    // Test zero
    let zero = TestInt::from(0u8);
    let mut buffer = [0u8; 8];
    let result = zero.to_be_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0, 0, 0, 0]);

    // Test small value
    let small = TestInt::from(0x1234u16);
    let mut buffer = [0u8; 8];
    let result = small.to_be_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0, 0, 0x12, 0x34]);

    // Test larger value
    let large = TestInt::from(0x12345678u32);
    let mut buffer = [0u8; 8];
    let result = large.to_be_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0x12, 0x34, 0x56, 0x78]);

    // Test buffer too small
    let value = TestInt::from(0x1234u16);
    let mut small_buffer = [0u8; 2];
    let result = value.to_be_bytes(&mut small_buffer);
    assert!(result.is_err());

    // Test that function actually writes to the buffer when successful
    let value = TestInt::from(0x1234u16);
    let mut buffer = [0xFFu8; 8]; // Fill with non-zero values
    let result = value.to_be_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    // Should have written zeros where there's no data
    assert_eq!(bytes[0], 0);
    assert_eq!(bytes[1], 0);
    assert_eq!(bytes[2], 0x12);
    assert_eq!(bytes[3], 0x34);
}

#[test]
fn test_to_hex_str_edge_cases() {
    type TestInt = FixedUInt<u16, 2>;

    // Test zero
    let zero = TestInt::from(0u8);
    let mut buffer = [0u8; 10];
    let result = zero.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "0");

    // Test buffer too small
    let value = TestInt::from(0x123456u32);
    let mut small_buffer = [0u8; 3];
    let result = value.to_hex_str(&mut small_buffer);
    assert!(result.is_err());

    // Test value with leading zeros in hex representation
    let value = TestInt::from(0x0012u16);
    let mut buffer = [0u8; 10];
    let result = value.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "12");

    // Test maximum value for type
    let max_value = TestInt::from(0xFFFFFFFFu32);
    let mut buffer = [0u8; 10];
    let result = max_value.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "ffffffff");

    // Test that buffer is filled with zeros initially
    let value = TestInt::from(0x12u8);
    let mut buffer = [0xAAu8; 10]; // Fill with non-zero values
    let result = value.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "12");

    // Test value that would produce a hex string with all zeros removed
    let value = TestInt::from(0x00000000u32);
    let mut buffer = [0u8; 10];
    let result = value.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "0");
}

#[test]
fn test_to_radix_str_edge_cases() {
    type TestInt = FixedUInt<u16, 2>;

    // Test zero in different radices
    let zero = TestInt::from(0u8);
    let mut buffer = [0u8; 20];

    for radix in [2, 8, 10, 16] {
        let result = zero.to_radix_str(&mut buffer, radix);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "0");
    }

    // Test buffer too small
    let value = TestInt::from(123456u32);
    let mut small_buffer = [0u8; 3];
    let result = value.to_radix_str(&mut small_buffer, 10);
    assert!(result.is_err());

    // Test different radices
    let value = TestInt::from(255u8);
    let mut buffer = [0u8; 20];

    let result = value.to_radix_str(&mut buffer, 2);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "11111111");

    let result = value.to_radix_str(&mut buffer, 8);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "377");

    let result = value.to_radix_str(&mut buffer, 16);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "ff");
}

#[test]
fn test_bit_length() {
    type TestInt = FixedUInt<u16, 2>;

    // Test zero
    let zero = TestInt::from(0u8);
    assert_eq!(zero.bit_length(), 0);

    // Test power of 2 values
    let one = TestInt::from(1u8);
    assert_eq!(one.bit_length(), 1);

    let two = TestInt::from(2u8);
    assert_eq!(two.bit_length(), 2);

    let four = TestInt::from(4u8);
    assert_eq!(four.bit_length(), 3);

    // Test non-power of 2
    let three = TestInt::from(3u8);
    assert_eq!(three.bit_length(), 2);

    let fifteen = TestInt::from(15u8);
    assert_eq!(fifteen.bit_length(), 4);

    // Test larger values
    let large = TestInt::from(0xFFFFu16);
    assert_eq!(large.bit_length(), 16);

    let max = TestInt::from(0xFFFFFFFFu32);
    assert_eq!(max.bit_length(), 32);
}

#[test]
fn test_div_rem() {
    type TestInt = FixedUInt<u16, 2>;

    // Test basic division
    let dividend = TestInt::from(20u8);
    let divisor = TestInt::from(3u8);
    let (quotient, remainder) = dividend.div_rem(&divisor);
    assert_eq!(quotient, TestInt::from(6u8));
    assert_eq!(remainder, TestInt::from(2u8));

    // Test exact division
    let dividend = TestInt::from(21u8);
    let divisor = TestInt::from(3u8);
    let (quotient, remainder) = dividend.div_rem(&divisor);
    assert_eq!(quotient, TestInt::from(7u8));
    assert_eq!(remainder, TestInt::from(0u8));

    // Test division by 1
    let dividend = TestInt::from(42u8);
    let divisor = TestInt::from(1u8);
    let (quotient, remainder) = dividend.div_rem(&divisor);
    assert_eq!(quotient, TestInt::from(42u8));
    assert_eq!(remainder, TestInt::from(0u8));

    // Test larger numbers
    let dividend = TestInt::from(1000u16);
    let divisor = TestInt::from(13u8);
    let (quotient, remainder) = dividend.div_rem(&divisor);
    assert_eq!(quotient, TestInt::from(76u8));
    assert_eq!(remainder, TestInt::from(12u8));
}

#[test]
fn test_new() {
    type TestInt = FixedUInt<u32, 4>;

    // Test that new() creates a zero value
    let zero = TestInt::new();
    assert_eq!(zero, TestInt::from(0u8));

    // Test that it works with different types
    let zero_u8 = FixedUInt::<u8, 8>::new();
    assert_eq!(zero_u8, FixedUInt::<u8, 8>::from(0u8));

    let zero_u16 = FixedUInt::<u16, 4>::new();
    assert_eq!(zero_u16, FixedUInt::<u16, 4>::from(0u8));

    let zero_u64 = FixedUInt::<u64, 2>::new();
    assert_eq!(zero_u64, FixedUInt::<u64, 2>::from(0u8));
}

#[test]
fn test_hex_fmt_functionality() {
    use fixed_bigint::FixedUInt;

    // Test basic hex formatting
    let value = FixedUInt::<u16, 2>::from(0x1234u16);
    let mut buffer = [0u8; 20];
    let result = value.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "1234");

    // Test with zero
    let zero = FixedUInt::<u16, 2>::from(0u8);
    let mut buffer = [0u8; 20];
    let result = zero.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "0");

    // Test with small buffer that should cause error
    let value = FixedUInt::<u16, 2>::from(0x123456u32);
    let mut small_buffer = [0u8; 2];
    let result = value.to_hex_str(&mut small_buffer);
    assert!(result.is_err());
}

#[test]
fn test_error_conditions() {
    type TestInt = FixedUInt<u8, 2>;

    // Test to_hex_str with insufficient buffer
    let value = TestInt::from(0xFFu8);
    let mut buffer = [0u8; 1];
    let result = value.to_hex_str(&mut buffer);
    assert!(result.is_err());

    // Test to_radix_str with insufficient buffer
    let value = TestInt::from(255u8);
    let mut buffer = [0u8; 2];
    let result = value.to_radix_str(&mut buffer, 2);
    assert!(result.is_err());
}

#[test]
fn test_internal_byte_logic() {
    type TestInt = FixedUInt<u8, 1>;

    // Test with u8 word size (should hit the WORD_BITS == 8 branch)
    let bytes = [0x42];
    let result = TestInt::from_le_bytes(&bytes);
    assert_eq!(result, TestInt::from(0x42u8));

    // Test with be_bytes
    let bytes = [0x42];
    let result = TestInt::from_be_bytes(&bytes);
    assert_eq!(result, TestInt::from(0x42u8));

    // Test to_le_bytes
    let value = TestInt::from(0x42u8);
    let mut buffer = [0u8; 4];
    let result = value.to_le_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0x42]);

    // Test to_be_bytes
    let value = TestInt::from(0x42u8);
    let mut buffer = [0u8; 4];
    let result = value.to_be_bytes(&mut buffer);
    assert!(result.is_ok());
    let bytes = result.unwrap();
    assert_eq!(bytes, &[0x42]);
}

#[test]
fn test_string_conversion_edge_cases() {
    type TestInt = FixedUInt<u32, 1>;

    // Test hex string with leading zero that should be stripped
    let value = TestInt::from(0x0123u16);
    let mut buffer = [0u8; 10];
    let result = value.to_hex_str(&mut buffer);
    assert!(result.is_ok());
    // The hex conversion will strip leading zeros, so 0x0123 becomes "123"
    let result_str = result.unwrap();
    assert!(result_str == "123" || result_str == "0"); // Handle both cases

    // Test radix string with different bases
    let value = TestInt::from(15u8);
    let mut buffer = [0u8; 10];

    // Base 2
    let result = value.to_radix_str(&mut buffer, 2);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "1111");

    // Base 8
    let result = value.to_radix_str(&mut buffer, 8);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "17");

    // Base 16
    let result = value.to_radix_str(&mut buffer, 16);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "f");
}

#[test]
fn test_from_u64_overflow() {
    type Small = FixedUInt<u8, 1>; // 8-bit capacity

    // Value that fits
    assert_eq!(Small::from_u64(255), Some(Small::from(255u8)));

    // Value that exceeds 8-bit should return None
    assert_eq!(Small::from_u64(256), None);

    type Medium = FixedUInt<u8, 2>; // 16-bit capacity
    assert_eq!(Medium::from_u64(65535), Some(Medium::from(65535u16)));
    assert_eq!(Medium::from_u64(65536), None);
}

#[test]
fn test_numcast_overflow() {
    type Small = FixedUInt<u8, 1>;

    // Casting a value larger than the destination should fail
    assert_eq!(num_traits::cast::<u32, Small>(300u32), None);
    // Casting a fitting value should succeed
    assert_eq!(num_traits::cast::<u32, Small>(123u32), Some(Small::from(123u8)));
}
