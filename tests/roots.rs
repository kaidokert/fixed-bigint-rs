use fixed_bigint::FixedUInt;
use num_integer::Roots;
use num_traits::{PrimInt, ToPrimitive};

#[test]
fn test_roots_integration() {
    type BigInt = FixedUInt<u32, 4>;

    // Test square roots
    assert_eq!(BigInt::from(144u32).sqrt(), BigInt::from(12u32));
    assert_eq!(BigInt::from(169u32).sqrt(), BigInt::from(13u32));
    assert_eq!(BigInt::from(200u32).sqrt(), BigInt::from(14u32)); // floor(sqrt(200)) = 14

    // Test cube roots
    assert_eq!(BigInt::from(125u32).cbrt(), BigInt::from(5u32));
    assert_eq!(BigInt::from(216u32).cbrt(), BigInt::from(6u32));
    assert_eq!(BigInt::from(1000u32).cbrt(), BigInt::from(10u32));

    // Test nth roots
    assert_eq!(BigInt::from(16u32).nth_root(4), BigInt::from(2u32));
    assert_eq!(BigInt::from(243u32).nth_root(5), BigInt::from(3u32));
    assert_eq!(BigInt::from(64u32).nth_root(6), BigInt::from(2u32));

    // Test with larger numbers
    let large_num = BigInt::from(1000000u32);
    assert_eq!(large_num.sqrt(), BigInt::from(1000u32));

    let even_larger = BigInt::from(1073741824u32); // 2^30
    assert_eq!(even_larger.nth_root(30), BigInt::from(2u32));
}

#[test]
fn test_roots_mathematical_property() {
    type BigInt = FixedUInt<u32, 2>;

    // Test that r^n <= x < (r+1)^n for various values
    for x in [10u32, 50u32, 100u32, 500u32, 1000u32, 5000u32] {
        for n in [2u32, 3u32, 4u32, 5u32] {
            let x_big = BigInt::from(x);
            let root = x_big.nth_root(n);

            // r^n <= x
            assert!(
                root.pow(n) <= x_big,
                "Failed: {}^{} <= {} (root={:?})",
                root.to_u32().unwrap_or(0),
                n,
                x,
                root
            );

            // (r+1)^n > x
            let root_plus_one = root + BigInt::from(1u32);
            assert!(
                root_plus_one.pow(n) > x_big,
                "Failed: {}^{} > {} (root+1={:?})",
                root_plus_one.to_u32().unwrap_or(0),
                n,
                x,
                root_plus_one
            );
        }
    }
}
