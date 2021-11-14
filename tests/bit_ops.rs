
#[cfg(test)]
use fixed_bigint::FixedUInt as Bn;

use std::ops::{BitAndAssign, BitOrAssign, BitXorAssign};

#[test]
fn test_and() {
	
	// 8 bit
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>
            + BitAndAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 0),
        (42, 1, 0),
        (42, 2, 2),
        (42, 10, 10),
        (42, 100, 32),
        (200, 8, 8),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a & b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitand(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a &= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitand_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();	

    // 16 bit
	fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>
            + BitAndAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 0),
        	(42, 1, 0),
        	(42, 2, 2),
        	(42, 10, 10),
        	(42, 100, 32),
        	(420, 1000, 416),
        	(200, 8, 8),
        	(2, 256, 0),
        	(500, 2, 0),
        	(500, 500, 500),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a & b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitand(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a &= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitand_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();	
    
    //32 bit
	fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>
            + BitAndAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 0),
        	(42, 1, 0),
        	(42, 2, 2),
        	(42, 10, 10),
        	(42, 100, 32),
        	(420, 1000, 416),
        	(200, 8, 8),
        	(2, 256, 0),
        	(500, 2, 0),
        	(500000, 2, 0),
        	(500, 500, 500),
        	(1000000000, 2, 0),
        	(2, 1000000000, 0),
        	(1000000000, 4, 0),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a & b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitand(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a &= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitand_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}

#[test]
fn test_or() {
	
	// 8 bit
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>
            + BitOrAssign,
    >() {
    	
    	let tests = [
			(42, 0, 42),
			(42, 1, 43),
			(42, 2, 42),
			(42, 10, 42),
			(42, 100, 110),
        	(200, 8, 200),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a | b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitor(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a |= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitor_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();	

    // 16 bit
	fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>
            + BitOrAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 42),
        	(42, 1, 43),
        	(42, 2, 42),
        	(42, 10, 42),
        	(42, 100, 110),
        	(420, 1000, 1004),
        	(200, 8, 200),
        	(2, 256, 258),
        	(500, 2, 502),
        	(500, 500, 500),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a | b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitor(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a |= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitor_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();	
    
    //32 bit
	fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>
            + BitOrAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 42),
        	(42, 1, 43),
       		(42, 2, 42),
       		(42, 10, 42),
       		(42, 100, 110),
       		(420, 1000, 1004),
       		(200, 8, 200),
       		(2, 256, 258),
       		(500, 2, 502),
       		(500000, 2, 500002),
       		(500, 500, 500),
       		(1000000000, 2, 1000000002),
       		(2, 1000000000, 1000000002),
       		(1000000000, 4, 1000000004),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a | b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitor(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a |= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitor_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}

#[test]
fn test_xor() {
	
	// 8 bit
    fn test_8_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u8>
            + BitXorAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 42),
        	(42, 1, 43),
        	(42, 2, 40),
        	(42, 10, 32),
        	(42, 100, 78),
        	(200, 8, 192),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a ^ b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitxor(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a ^= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitxor_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_8_bit::<u8>();
    test_8_bit::<Bn<u8, 1>>();	

    // 16 bit
	fn test_16_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u16>
            + BitXorAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 42),
        	(42, 1, 43),
        	(42, 2, 40),
        	(42, 10, 32),
        	(42, 100, 78),
        	(200, 8, 192),
        	(420, 1000, 588),
        	(2, 256, 258),
        	(500, 2, 502),
        	(500, 500, 0),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a ^ b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitxor(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a ^= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitxor_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_16_bit::<u16>();
    test_16_bit::<Bn<u8, 2>>();
    test_16_bit::<Bn<u16, 1>>();	
    
    //32 bit
	fn test_32_bit<
        INT: num_traits::PrimInt<FromStrRadixErr = core::num::ParseIntError>
            + core::fmt::Debug
            + From<u32>
            + BitXorAssign,
    >() {
    	
    	let tests = [
        	(42, 0, 42),
        	(42, 1, 43),
        	(42, 2, 40),
        	(42, 10, 32),
        	(42, 100, 78),
        	(200, 8, 192),
        	(420, 1000, 588),
        	(2, 256, 258),
        	(500, 2, 502),
        	(500, 500, 0),
        	(500000, 2, 500002),
        	(1000000000, 2, 1000000002),
        	(2, 1000000000, 1000000002),
        	(1000000000, 4, 1000000004),
        ];
    
        for (a, b, res) in &tests {
        	let b_a = Into::<INT>::into(*a);
        	let b_b = Into::<INT>::into(*b);
        	
        	let b_res = b_a ^ b_b;
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let b_res = b_a.bitxor(b_b);
        	assert_eq!(b_res.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a ^= b_b;
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        	
        	let mut b_a = Into::<INT>::into(*a);
        	b_a.bitxor_assign(b_b);
        	assert_eq!(b_a.to_u64().unwrap(), *res);
        }
    }
    
    test_32_bit::<u32>();
    test_32_bit::<Bn<u8, 4>>();
    test_32_bit::<Bn<u16, 2>>();
    test_32_bit::<Bn<u32, 1>>();
}