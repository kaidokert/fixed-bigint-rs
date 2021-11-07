// 
// MIT License
// 
// Copyright (c) 2021 Igram, D.O.O.
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

#[cfg(test)]
use fixed_bigint::FixedUInt as Bn;

use num_traits::{FromPrimitive, ToPrimitive};
use std::ops::{BitOr, BitOrAssign};


#[test]
fn test_or() {
	let a: Bn<u8, 1> = 2u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    assert_eq!(a | b, 3u8.into());
    assert_eq!(a.bitor(b), 3u8.into());
    
    let a = Bn::<u8, 2>::from_u64(3).unwrap();
    let b = Bn::<u8, 2>::from_u64(4).unwrap();
    let r = a | b;
    assert_eq!(r.to_u16().unwrap(), 7);
    let r = a.bitor(b);
    assert_eq!(r.to_u16().unwrap(), 7);
    
    let a = Bn::<u8, 2>::from_u64(300).unwrap();
    let b = Bn::<u8, 2>::from_u64(4).unwrap();
    let r = a | b;
    assert_eq!(r.to_u64().unwrap(), 300);
    let r = a.bitor(b);
    assert_eq!(r.to_u64().unwrap(), 300);
    
    let tests = [
        (0x010203u64, 0x1020u64, 0x11223u64),
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
        let b_a = Bn::<u8, 8>::from_u64(*a).unwrap();
        let b_b = Bn::<u8, 8>::from_u64(*b).unwrap();
        let b_res = b_a | b_b;
        assert_eq!(b_res.to_u64().unwrap(), *res);
    }
    for (a, b, res) in &tests {
        let b_a = Bn::<u32, 2>::from_u64(*a).unwrap();
        let b_b = Bn::<u32, 2>::from_u64(*b).unwrap();
        let b_res = b_a | b_b;
        assert_eq!(b_res.to_u64().unwrap(), *res);
    }
           
    for (a, b, res) in &tests {
        let b_a = Bn::<u8, 8>::from_u64(*a).unwrap();
        let b_b = Bn::<u8, 8>::from_u64(*b).unwrap();
        let b_res = b_a.bitor(b_b);
        assert_eq!(b_res.to_u64().unwrap(), *res);
    }
    for (a, b, res) in &tests {
        let b_a = Bn::<u32, 2>::from_u64(*a).unwrap();
        let b_b = Bn::<u32, 2>::from_u64(*b).unwrap();
        let b_res = b_a.bitor(b_b);
        assert_eq!(b_res.to_u64().unwrap(), *res);
    }
}

#[test]
fn test_or_assign() {
	let mut a: Bn<u8, 1> = 2u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    a |= b;
    assert_eq!(a, 3u8.into());
    
    let mut a: Bn<u8, 1> = 2u8.into();
    let b: Bn<u8, 1> = 3u8.into();
    a.bitor_assign(b);
    assert_eq!(a, 3u8.into());

        
    let mut a = Bn::<u8, 2>::from_u64(3).unwrap();
    let b = Bn::<u8, 2>::from_u64(4).unwrap();
    a |= b;
    assert_eq!(a.to_u16().unwrap(), 7);
    let mut a = Bn::<u8, 2>::from_u64(3).unwrap();
    a.bitor_assign(b);
    assert_eq!(a.to_u16().unwrap(), 7);
    
    let mut a = Bn::<u8, 2>::from_u64(300).unwrap();
    let b = Bn::<u8, 2>::from_u64(4).unwrap();
    a |= b;
    assert_eq!(a.to_u64().unwrap(), 300);
    let mut a = Bn::<u8, 2>::from_u64(300).unwrap();
    a.bitor_assign(b);
    assert_eq!(a.to_u64().unwrap(), 300);

    
    let tests = [
        (0x010203u64, 0x1020u64, 0x11223u64),
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
        let mut b_a = Bn::<u8, 8>::from_u64(*a).unwrap();
        let b_b = Bn::<u8, 8>::from_u64(*b).unwrap();
        b_a |= b_b;
        assert_eq!(b_a.to_u64().unwrap(), *res);
    }
    
    for (a, b, res) in &tests {
        let mut b_a = Bn::<u8, 8>::from_u64(*a).unwrap();
        let b_b = Bn::<u8, 8>::from_u64(*b).unwrap();
        b_a.bitor_assign(b_b);
        assert_eq!(b_a.to_u64().unwrap(), *res);
    }
    
    for (a, b, res) in &tests {
        let mut b_a = Bn::<u32, 2>::from_u64(*a).unwrap();
        let b_b = Bn::<u32, 2>::from_u64(*b).unwrap();
        b_a |= b_b;
        assert_eq!(b_a.to_u64().unwrap(), *res);
    }
           
    for (a, b, res) in &tests {
        let mut b_a = Bn::<u32, 2>::from_u64(*a).unwrap();
        let b_b = Bn::<u32, 2>::from_u64(*b).unwrap();
        b_a.bitor_assign(b_b);
        assert_eq!(b_a.to_u64().unwrap(), *res);
    }
    
}