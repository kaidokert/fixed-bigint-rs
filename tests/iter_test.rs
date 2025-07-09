use fixed_bigint::FixedUInt;

#[test]
fn test_sum() {
    type TestInt = FixedUInt<u32, 2>;

    // Test sum of values
    let values = vec![
        TestInt::from(1u8),
        TestInt::from(2u8),
        TestInt::from(3u8),
        TestInt::from(4u8),
        TestInt::from(5u8),
    ];

    let sum: TestInt = values.iter().cloned().sum();
    assert_eq!(sum, TestInt::from(15u8));

    // Test sum of references
    let sum_refs: TestInt = values.iter().sum();
    assert_eq!(sum_refs, TestInt::from(15u8));

    // Test empty iterator
    let empty_vec: Vec<TestInt> = vec![];
    let empty_sum: TestInt = empty_vec.iter().cloned().sum();
    assert_eq!(empty_sum, TestInt::from(0u8));
}

#[test]
fn test_product() {
    type TestInt = FixedUInt<u32, 2>;

    // Test product of values
    let values = vec![TestInt::from(2u8), TestInt::from(3u8), TestInt::from(4u8)];

    let product: TestInt = values.iter().cloned().product();
    assert_eq!(product, TestInt::from(24u8));

    // Test product of references
    let product_refs: TestInt = values.iter().product();
    assert_eq!(product_refs, TestInt::from(24u8));

    // Test empty iterator
    let empty_vec: Vec<TestInt> = vec![];
    let empty_product: TestInt = empty_vec.iter().cloned().product();
    assert_eq!(empty_product, TestInt::from(1u8));
}

#[test]
fn test_sum_large_numbers() {
    type TestInt = FixedUInt<u64, 2>;

    let values = vec![
        TestInt::from(1000000u32),
        TestInt::from(2000000u32),
        TestInt::from(3000000u32),
    ];

    let sum: TestInt = values.iter().cloned().sum();
    assert_eq!(sum, TestInt::from(6000000u32));
}

#[test]
fn test_product_large_numbers() {
    type TestInt = FixedUInt<u64, 2>;

    let values = vec![
        TestInt::from(10u8),
        TestInt::from(20u8),
        TestInt::from(30u8),
    ];

    let product: TestInt = values.iter().cloned().product();
    // Create expected value more directly
    let expected = TestInt::from(10u8) * TestInt::from(20u8) * TestInt::from(30u8);
    assert_eq!(product, expected); // 10 * 20 * 30 = 6000
}

#[test]
fn test_sum_different_types() {
    // Test with different machine word types
    type TestInt8 = FixedUInt<u8, 4>;
    type TestInt16 = FixedUInt<u16, 2>;

    let values8 = vec![
        TestInt8::from(10u8),
        TestInt8::from(20u8),
        TestInt8::from(30u8),
    ];
    let sum8: TestInt8 = values8.iter().cloned().sum();
    assert_eq!(sum8, TestInt8::from(60u8));

    let values16 = vec![
        TestInt16::from(100u8),
        TestInt16::from(200u8),
        TestInt16::from(255u8),
    ];
    let sum16: TestInt16 = values16.iter().cloned().sum();
    assert_eq!(sum16, TestInt16::from(555u16)); // 100 + 200 + 255 = 555
}

#[test]
fn test_chained_operations() {
    type TestInt = FixedUInt<u32, 2>;

    let values = vec![
        TestInt::from(1u8),
        TestInt::from(2u8),
        TestInt::from(3u8),
        TestInt::from(4u8),
        TestInt::from(5u8),
    ];

    // Test sum after filtering
    let sum_evens: TestInt = values
        .iter()
        .filter(|&&x| x % TestInt::from(2u8) == TestInt::from(0u8))
        .cloned()
        .sum();
    assert_eq!(sum_evens, TestInt::from(6u8)); // 2 + 4 = 6

    // Test product after mapping
    let product_doubled: TestInt = values
        .iter()
        .take(3)
        .map(|&x| x * TestInt::from(2u8))
        .product();
    assert_eq!(product_doubled, TestInt::from(48u8)); // (1*2) * (2*2) * (3*2) = 2 * 4 * 6 = 48
}
