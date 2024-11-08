//		Packages

use super::*;
use bytes::BytesMut;
use claims::{assert_err, assert_err_eq, assert_ok_eq};
use core::cmp::Ordering;
use rubedo::sugar::s;
use std::collections::HashSet;
use tokio_postgres::types::{Type, IsNull};
use typenum::U63;



//		Type aliases

#[expect(non_camel_case_types, reason = "To fit with other primitives")]
type u63 = Int<U63, false>;



//		Tests

mod constructors {
	use super::*;
	
	//		new																	
	#[test]
	fn new__valid() {
		assert_ok_eq!(u63::new(0_i64.to_le_bytes().into()),    u63::min_value());
		assert_ok_eq!(u63::new(i64::MAX.to_le_bytes().into()), u63::max_value());
	}
	#[test]
	fn new__invalid() {
		let err1 = u63::new(u64::MAX.to_le_bytes().into());
		assert_err_eq!(&err1, &ConversionError::ValueTooLarge);
		assert_eq!(err1.unwrap_err().to_string(), s!("Value too large"));
		
		let err2 = u63::new((i64::MAX as u64 + 1).to_le_bytes().into());
		assert_err_eq!(&err2, &ConversionError::ValueTooLarge);
		assert_eq!(err2.unwrap_err().to_string(), s!("Value too large"));
	}
}

mod public_methods {
	use super::*;
	
	//		as_array															
	#[test]
	fn as_array__normal() {
		let value = u63::try_from(42).unwrap();
		let array = value.as_array();
		assert_eq!(array[0],         42);
		assert_eq!(array.len(),      8);
		assert_eq!(array.as_slice(), &[42, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn as_array__min() {
		let value = u63::min_value();
		let array = value.as_array();
		assert_eq!(array[0],         0);
		assert_eq!(array.len(),      8);
		assert_eq!(array.as_slice(), &[0, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn as_array__max() {
		let value = u63::max_value();
		let array = value.as_array();
		assert_eq!(array[0],         255);
		assert_eq!(array.len(),      8);
		assert_eq!(array.as_slice(), &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
	}
	
	//		as_slice															
	#[test]
	fn as_slice__normal() {
		let value = u63::try_from(42).unwrap();
		let slice = value.as_slice();
		assert_eq!(slice[0],    42);
		assert_eq!(slice.len(), 8);
		assert_eq!(slice,       &[42, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn as_slice__min() {
		let value = u63::min_value();
		let slice = value.as_slice();
		assert_eq!(slice[0],    0);
		assert_eq!(slice.len(), 8);
		assert_eq!(slice,       &[0, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn as_slice__max() {
		let value = u63::max_value();
		let slice = value.as_slice();
		assert_eq!(slice[0],    255);
		assert_eq!(slice.len(), 8);
		assert_eq!(slice,       &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
	}
	
	//		bit																	
	#[test]
	fn bit__normal() {
		let value = u63::try_from(0b101).unwrap();
		assert!( value.bit(0));
		assert!(!value.bit(1));
		assert!( value.bit(2));
	}
	#[test]
	fn bit__out_of_range() {
		let value = u63::try_from(0b101).unwrap();
		assert!(!value.bit(63));
		assert!(!value.bit(64));
	}
	
	//		bits																
	#[test]
	fn bits__normal() {
		let value1 = u63::try_from(0b1111_0000).unwrap();
		assert_eq!(value1.bits(0..4), vec![false, false, false, false]);
		assert_eq!(value1.bits(4..8), vec![true, true, true, true]);
		assert_eq!(value1.bits(1..2), vec![false]);
		
		let value2 = u63::try_from(0b11011).unwrap();
		assert_eq!(value2.bits(0..5), vec![true, true, false, true, true]);
	}
	#[test]
	#[expect(clippy::reversed_empty_ranges, reason = "Specifically testing empty ranges")]
	fn bits__invalid_range() {
		let value = u63::max_value();
		assert!(value.bits( 5..3).is_empty());   //  Start > end
		assert!(value.bits(63..65).is_empty());  //  End > BITS
		assert!(value.bits(65..70).is_empty());  //  Start >= BITS
	}
	#[test]
	fn bits__multi_byte() {
		let mut value = u63::zero();
		_ = value.set_bit(15, true);
		assert_eq!(value.bits(14..17), vec![false, true, false]);
	}
	#[test]
	fn bits__range_syntax() {
		let value = u63::try_from(0b010_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1010_u64).unwrap();
		assert_eq!(value.bits(..).len(), 63);
		assert_eq!(value.bits(60..),     vec![false, true, false]);
		assert_eq!(value.bits(  ..4),    vec![false, true, false, true]);
		assert_eq!(value.bits(  ..=3),   vec![false, true, false, true]);
		assert_eq!(value.bits( 1..4),    vec![true, false, true]);
	}
	
	//		checked_add															
	#[test]
	fn checked_add__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.checked_add(b), Some(u63::try_from(8).unwrap()));
	}
	#[test]
	fn checked_add__at_max() {
		let a = u63::try_from(i64::MAX as u64 - 1).unwrap();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.checked_add(b), Some(u63::max_value()));
	}
	#[test]
	fn checked_add__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.checked_add(b), None);
	}
	
	//		checked_div															
	#[test]
	fn checked_div__normal() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.checked_div(b), Some(u63::try_from(3).unwrap()));
	}
	#[test]
	fn checked_div__by_zero() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(0).unwrap();
		assert_eq!(a.checked_div(b), None);
	}
	
	//		checked_mul															
	#[test]
	fn checked_mul__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.checked_mul(b), Some(u63::try_from(15).unwrap()));
	}
	#[test]
	fn checked_mul__at_max() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.checked_mul(b), Some(u63::max_value()));
	}
	#[test]
	fn checked_mul__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.checked_mul(b), None);
	}
	
	//		checked_pow															
	#[test]
	fn checked_pow__normal() {
		assert_eq!(u63::try_from(2).unwrap().checked_pow(3), Some(u63::try_from(8).unwrap()));
	}
	#[test]
	fn checked_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::try_from(2).unwrap().checked_pow(max_power), Some(u63::try_from(1_u64 << max_power).unwrap()));
	}
	#[test]
	fn checked_pow__overflow() {
		assert_eq!(u63::try_from(2).unwrap().checked_pow(63), None);
	}
	#[test]
	fn checked_pow__zero() {
		let base = u63::try_from(0).unwrap();
		assert_eq!(base.checked_pow(0), Some(u63::try_from(1).unwrap()));
		assert_eq!(base.checked_pow(1), Some(u63::try_from(0).unwrap()));
	}
	
	//		checked_rem															
	#[test]
	fn checked_rem__normal() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(4).unwrap();
		assert_eq!(a.checked_rem(b), Some(u63::try_from(3).unwrap()));
	}
	#[test]
	fn checked_rem__by_zero() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(0).unwrap();
		assert_eq!(a.checked_rem(b), None);
	}
	
	//		checked_sub															
	#[test]
	fn checked_sub__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.checked_sub(b), Some(u63::try_from(2).unwrap()));
	}
	#[test]
	fn checked_sub__at_min() {
		let a = u63::try_from(1).unwrap();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.checked_sub(b), Some(u63::min_value()));
	}
	#[test]
	fn checked_sub__underflow() {
		let a = u63::min_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.checked_sub(b), None);
	}
	
	//		count_ones															
	#[test]
	fn count_ones__zero() {
		assert_eq!(u63::min_value().count_ones(), 0);
	}
	#[test]
	fn count_ones__one() {
		assert_eq!(u63::try_from(1).unwrap().count_ones(), 1);
	}
	#[test]
	fn count_ones__some() {
		assert_eq!(u63::try_from(0b1010_1010).unwrap().count_ones(), 4);
	}
	#[test]
	fn count_ones__all() {
		assert_eq!(u63::max_value().count_ones(), 63);
	}
	
	//		count_zeroes														
	#[test]
	fn count_zeros__zero() {
		assert_eq!(u63::max_value().count_zeros(), 0);
	}
	#[test]
	fn count_zeros__one() {
		assert_eq!(u63::try_from(i64::MAX as u64 - 1).unwrap().count_zeros(), 1);
	}
	#[test]
	fn count_zeros__some() {
		//	63 - 4 ones
		assert_eq!(u63::try_from(0b1010_1010).unwrap().count_zeros(), 59);
	}
	#[test]
	fn count_zeros__all() {
		//	One less than u64 due to highest bit
		assert_eq!(u63::min_value().count_zeros(), 63);
	}
	
	//		from_be_bytes														
	#[test]
	fn from_be_bytes__normal() {
		let bytes = [0, 0, 0, 0, 0, 0, 0x12, 0x34];
		assert_ok_eq!(u63::from_be_bytes(&bytes), u63::try_from(0x1234).unwrap());
	}
	#[test]
	fn from_be_bytes__wrong_size() {
		let bytes = [0x12, 0x34];
		assert_err_eq!(u63::from_be_bytes(&bytes), ConversionError::ValueTooLarge);
	}
	#[test]
	fn from_be_bytes__roundtrip() {
		let original = u63::try_from(0x1234_5678).unwrap();
		let bytes    = original.to_be_bytes();
		let value    = u63::from_be_bytes(bytes.as_slice()).unwrap();
		assert_eq!(value, original);
	}
	
	//		from_json															
	#[test]
	fn from_json__valid() {
		assert_ok_eq!(u63::from_json("42"),      u63::try_from(42).unwrap());
		assert_ok_eq!(u63::from_json(r#""42""#), u63::try_from(42).unwrap());
	}
	#[test]
	fn from_json__invalid() {
		assert_err!(u63::from_json("invalid"));
		assert_err!(u63::from_json("-1"));
		assert_err!(u63::from_json("9999999999999999999999"));
	}
	
	//		from_le_bytes														
	#[test]
	fn from_le_bytes__normal() {
		let bytes = [0x34, 0x12, 0, 0, 0, 0, 0, 0];
		assert_ok_eq!(u63::from_le_bytes(&bytes), u63::try_from(0x1234).unwrap());
	}
	#[test]
	fn from_le_bytes__wrong_size() {
		let bytes = [0x34, 0x12];
		assert_err_eq!(u63::from_le_bytes(&bytes), ConversionError::ValueTooLarge);
	}
	#[test]
	fn from_le_bytes__roundtrip() {
		let original = u63::try_from(0x1234_5678).unwrap();
		let bytes    = original.to_le_bytes();
		let value    = u63::from_le_bytes(bytes.as_slice()).unwrap();
		assert_eq!(value, original);
	}
	
	//		into_array															
	#[test]
	fn into_array__normal() {
		let value = u63::try_from(42).unwrap();
		let array = value.into_array();
		assert_eq!(array[0],         42);
		assert_eq!(array.len(),      8);
		assert_eq!(array.as_slice(), &[42, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn into_array__min() {
		let value = u63::min_value();
		let array = value.into_array();
		assert_eq!(array[0],         0);
		assert_eq!(array.len(),      8);
		assert_eq!(array.as_slice(), &[0, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn into_array__max() {
		let value = u63::max_value();
		let array = value.into_array();
		assert_eq!(array[0],         255);
		assert_eq!(array.len(),      8);
		assert_eq!(array.as_slice(), &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
	}
	
	//		into_vec															
	#[test]
	fn into_vec__normal() {
		let value = u63::try_from(42).unwrap();
		let vec   = value.into_vec();
		assert_eq!(vec[0],    42);
		assert_eq!(vec.len(), 8);
		assert_eq!(vec,       vec![42, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn into_vec__min() {
		let value = u63::min_value();
		let vec   = value.into_vec();
		assert_eq!(vec[0],    0);
		assert_eq!(vec.len(), 8);
		assert_eq!(vec,       vec![0, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn into_vec__max() {
		let value = u63::max_value();
		let vec   = value.into_vec();
		assert_eq!(vec[0],    255);
		assert_eq!(vec.len(), 8);
		assert_eq!(vec,       vec![0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
	}
	
	//		is_negative															
	#[test]
	fn is_negative() {
		assert!(!u63::min_value().is_negative());
		assert!(!u63::try_from(0).unwrap().is_negative());
		assert!(!u63::try_from(1).unwrap().is_negative());
		assert!(!u63::try_from(42).unwrap().is_negative());
		assert!(!u63::max_value().is_negative());
	}
	
	//		is_power_of_two														
	#[test]
	fn is_power_of_two() {
		assert!(!u63::min_value().is_power_of_two());
		assert!( u63::try_from(1).unwrap().is_power_of_two());
		assert!( u63::try_from(2).unwrap().is_power_of_two());
		assert!(!u63::try_from(42).unwrap().is_power_of_two());
		assert!( u63::try_from(1_u64 << 62).unwrap().is_power_of_two());
	}
	
	//		is_zero																
	#[test]
	fn is_zero() {
		assert!( u63::min_value().is_zero());
		assert!( u63::try_from(0).unwrap().is_zero());
		assert!(!u63::try_from(1).unwrap().is_zero());
		assert!(!u63::try_from(42).unwrap().is_zero());
		assert!(!u63::max_value().is_zero());
	}
	
	//		leading_ones														
	#[test]
	fn leading_ones__all() {
		assert_eq!(u63::max_value().leading_ones(), 63);
	}
	#[test]
	fn leading_ones__none() {
		assert_eq!(u63::min_value().leading_ones(), 0);
	}
	#[test]
	fn leading_ones__some() {
		assert_eq!(u63::try_from(1).unwrap().leading_ones(),      0);
		assert_eq!(u63::try_from(0b1010).unwrap().leading_ones(), 0);
		assert_eq!((!(u63::max_value() >> 2)).leading_ones(),     2);
	}
	
	//		leading_zeros														
	#[test]
	fn leading_zeros__all() {
		assert_eq!(u63::min_value().leading_zeros(), 63);
	}
	#[test]
	fn leading_zeros__none() {
		assert_eq!(u63::max_value().leading_zeros(), 0);
	}
	#[test]
	fn leading_zeros__some() {
		assert_eq!(u63::try_from(1).unwrap().leading_zeros(),      62);
		assert_eq!(u63::try_from(0b1010).unwrap().leading_zeros(), 59);
		assert_eq!((u63::max_value() >> 2).leading_zeros(),        2);
	}
	
	//		max_value															
	#[test]
	fn max_value() {
		assert_eq!(u63::max_value(), u63::try_from(u64::MAX / 2).unwrap());
	}
	
	//		min_value															
	#[test]
	fn min_value() {
		assert_eq!(u63::min_value(), u63::try_from(0).unwrap());
	}
	
	//		one																	
	#[test]
	fn one() {
		assert_eq!(u63::one(), u63::try_from(1).unwrap());
	}
	
	//		overflowing_add														
	#[test]
	fn overflowing_add__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.overflowing_add(b), (u63::try_from(8).unwrap(), false));
	}
	#[test]
	fn overflowing_add__at_max() {
		let a = u63::try_from(i64::MAX as u64 - 1).unwrap();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.overflowing_add(b), (u63::max_value(), false));
	}
	#[test]
	fn overflowing_add__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.overflowing_add(b), (u63::min_value(), true));
	}
	
	//		overflowing_div														
	#[test]
	fn overflowing_div__normal() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.overflowing_div(b), (u63::try_from(3).unwrap(), false));
	}
	#[test]
	fn overflowing_div__by_zero() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(0).unwrap();
		assert_eq!(a.overflowing_div(b), (u63::max_value(), true));
	}
	
	//		overflowing_mul														
	#[test]
	fn overflowing_mul__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.overflowing_mul(b), (u63::try_from(15).unwrap(), false));
	}
	#[test]
	fn overflowing_mul__at_max() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.overflowing_mul(b), (u63::max_value(), false));
	}
	#[test]
	fn overflowing_mul__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.overflowing_mul(b), (u63::max_value() - u63::try_from(1).unwrap(), true));
	}
	
	//		overflowing_pow														
	#[test]
	fn overflowing_pow__normal() {
		assert_eq!(u63::try_from(2).unwrap().overflowing_pow(3), (u63::try_from(8).unwrap(), false));
	}
	#[test]
	fn overflowing_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::try_from(2).unwrap().overflowing_pow(max_power), (u63::try_from(1_u64 << max_power).unwrap(), false));
	}
	#[test]
	fn overflowing_pow__overflow() {
		assert_eq!(u63::try_from(2).unwrap().overflowing_pow(63), (u63::min_value(), true));
	}
	
	//		overflowing_rem														
	#[test]
	fn overflowing_rem__normal() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(4).unwrap();
		assert_eq!(a.overflowing_rem(b), (u63::try_from(3).unwrap(), false));
	}
	#[test]
	fn overflowing_rem__by_zero() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(0).unwrap();
		assert_eq!(a.overflowing_rem(b), (u63::max_value(), true));
	}
	
	//		overflowing_sub														
	#[test]
	fn overflowing_sub__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.overflowing_sub(b), (u63::try_from(2).unwrap(), false));
	}
	#[test]
	fn overflowing_sub__at_min() {
		let a = u63::try_from(1).unwrap();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.overflowing_sub(b), (u63::min_value(), false));
	}
	#[test]
	fn overflowing_sub__underflow() {
		let a = u63::min_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.overflowing_sub(b), (u63::max_value(), true));
	}
	
	//		parse																
	#[test]
	fn parse__valid() {
		assert_ok_eq!(u63::parse( "0"),                  u63::min_value());
		assert_ok_eq!(u63::parse("42"),                  u63::try_from(42).unwrap());
		assert_ok_eq!(u63::parse(&i64::MAX.to_string()), u63::max_value());
	}
	#[test]
	fn parse__invalid_format() {
		let err1 = u63::parse("abc");
		assert_err_eq!(&err1, &ConversionError::InvalidRadix('a', 10));
		assert_eq!(err1.unwrap_err().to_string(), s!("Invalid digit for base 10: a"));
		
		let err2 = u63::parse("12.34");
		assert_err_eq!(&err2, &ConversionError::InvalidDigit('.'));
		assert_eq!(err2.unwrap_err().to_string(), s!("Invalid digit: ."));
	}
	#[test]
	fn parse__too_large() {
		assert_err_eq!(u63::parse(&u64::MAX.to_string()), ConversionError::ValueTooLarge);
	}
	
	//		reverse_bits														
	#[test]
	fn reverse_bits__zero() {
		assert_eq!(u63::min_value().reverse_bits(), u63::min_value());
	}
	#[test]
	fn reverse_bits__one() {
		assert_eq!(u63::try_from(1).unwrap().reverse_bits(), u63::try_from(1_u64 << 62).unwrap());
	}
	#[test]
	fn reverse_bits__pattern() {
		assert_eq!(
			u63::try_from(0b1010_u64).unwrap().reverse_bits(),
			u63::try_from(0b0010_1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_u64).unwrap()
		);
	}
	#[test]
	fn reverse_bits__all() {
		assert_eq!(u63::max_value().reverse_bits(), u63::max_value());
	}
	
	//		rotate_left															
	#[test]
	fn rotate_left__zero() {
		let value = u63::try_from(0b1).unwrap();
		assert_eq!(value.rotate_left(0), value);
	}
	#[test]
	fn rotate_left__one() {
		assert_eq!(u63::try_from(0b1).unwrap().rotate_left(1), u63::try_from(0b10).unwrap());
	}
	#[test]
	fn rotate_left__many() {
		assert_eq!(u63::try_from(0b1).unwrap().rotate_left(4), u63::try_from(0b10000).unwrap());
	}
	#[test]
	fn rotate_left__full_rotation() {
		let value = u63::try_from(0b1).unwrap();
		assert_eq!(value.rotate_left(63), value);
	}
	
	//		rotate_right														
	#[test]
	fn rotate_right__zero() {
		let value = u63::try_from(0b1000).unwrap();
		assert_eq!(value.rotate_right(0), value);
	}
	#[test]
	fn rotate_right__one() {
		assert_eq!(u63::try_from(0b1000).unwrap().rotate_right(1), u63::try_from(0b100).unwrap());
	}
	#[test]
	fn rotate_right__many() {
		assert_eq!(u63::try_from(0b1000).unwrap().rotate_right(2), u63::try_from(0b10).unwrap());
	}
	#[test]
	fn rotate_right__full_rotation() {
		let value = u63::try_from(0b1000).unwrap();
		assert_eq!(value.rotate_right(63), value);
	}
	
	//		saturating_add														
	#[test]
	fn saturating_add__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.saturating_add(b), u63::try_from(8).unwrap());
	}
	#[test]
	fn saturating_add__at_max() {
		let a = u63::try_from(i64::MAX as u64 - 1).unwrap();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.saturating_add(b), u63::max_value());
	}
	#[test]
	fn saturating_add__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.saturating_add(b), u63::max_value());
	}
	
	//		saturating_div														
	#[test]
	fn saturating_div__normal() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.saturating_div(b), u63::try_from(3).unwrap());
	}
	#[test]
	fn saturating_div__by_zero() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(0).unwrap();
		assert_eq!(a.saturating_div(b), u63::max_value());
	}
	
	//		saturating_mul														
	#[test]
	fn saturating_mul__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.saturating_mul(b), u63::try_from(15).unwrap());
	}
	#[test]
	fn saturating_mul__at_max() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.saturating_mul(b), u63::max_value());
	}
	#[test]
	fn saturating_mul__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.saturating_mul(b), u63::max_value());
	}
	
	//		saturating_pow														
	#[test]
	fn saturating_pow__normal() {
		assert_eq!(u63::try_from(2).unwrap().saturating_pow(3), u63::try_from(8).unwrap());
	}
	#[test]
	fn saturating_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::try_from(2).unwrap().saturating_pow(max_power), u63::try_from(1_u64 << max_power).unwrap());
	}
	#[test]
	fn saturating_pow__overflow() {
		assert_eq!(u63::try_from(2).unwrap().saturating_pow(63), u63::max_value());
	}
	#[test]
	fn saturating_pow__zero() {
		let base = u63::try_from(0).unwrap();
		assert_eq!(base.saturating_pow(0), u63::try_from(1).unwrap());
		assert_eq!(base.saturating_pow(1), u63::try_from(0).unwrap());
	}
	
	//		saturating_sub														
	#[test]
	fn saturating_sub__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.saturating_sub(b), u63::try_from(2).unwrap());
	}
	#[test]
	fn saturating_sub__at_min() {
		let a = u63::try_from(1).unwrap();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.saturating_sub(b), u63::min_value());
	}
	#[test]
	fn saturating_sub__underflow() {
		let a = u63::min_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.saturating_sub(b), u63::min_value());
	}
	
	//		set_bit																
	#[test]
	fn set_bit__normal() {
		let mut value = u63::try_from(0b101).unwrap();
		assert!(value.set_bit(0, false));
		assert!(value.set_bit(1, true));
		assert!(value.set_bit(2, true));
		assert_eq!(value, u63::try_from(0b110).unwrap());
	}
	#[test]
	fn set_bit__out_of_range() {
		let mut value = u63::try_from(0b101).unwrap();
		assert!(!value.set_bit(64, true));
		assert_eq!(value, u63::try_from(0b101).unwrap());
	}
	
	//		to_be_bytes															
	#[test]
	fn to_be_bytes() {
		let value = u63::try_from(0x1234).unwrap();
		assert_eq!(value.to_be_bytes().as_slice(),            &[0, 0, 0, 0, 0, 0, 0x12, 0x34]);
		assert_eq!(u63::zero().to_be_bytes().as_slice(),      &[0; 8]);
		assert_eq!(u63::max_value().to_be_bytes().as_slice(), &[0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]);
	}
	
	//		to_json																
	#[test]
	fn to_json() {
		assert_ok_eq!(u63::try_from(42).unwrap().to_json(), "42");
	}
	
	//		to_le_bytes															
	#[test]
	fn to_le_bytes() {
		let value = u63::try_from(0x1234).unwrap();
		assert_eq!(value.to_le_bytes().as_slice(),            &[0x34, 0x12, 0, 0, 0, 0, 0, 0]);
		assert_eq!(u63::zero().to_le_bytes().as_slice(),      &[0; 8]);
		assert_eq!(u63::max_value().to_le_bytes().as_slice(), &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
	}
	
	//		to_vec																
	#[test]
	fn to_vec__normal() {
		let value = u63::try_from(42).unwrap();
		let vec   = value.to_vec();
		assert_eq!(vec[0],    42);
		assert_eq!(vec.len(), 8);
		assert_eq!(vec,       vec![42, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn to_vec__min() {
		let value = u63::min_value();
		let vec   = value.to_vec();
		assert_eq!(vec[0],    0);
		assert_eq!(vec.len(), 8);
		assert_eq!(vec,       vec![0, 0, 0, 0, 0, 0, 0, 0]);
	}
	#[test]
	fn to_vec__max() {
		let value = u63::max_value();
		let vec   = value.to_vec();
		assert_eq!(vec[0],    255);
		assert_eq!(vec.len(), 8);
		assert_eq!(vec,       vec![0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
	}
	
	//		trailing_ones														
	#[test]
	fn trailing_ones__all() {
		assert_eq!(u63::max_value().trailing_ones(), 63);
	}
	#[test]
	fn trailing_ones__none() {
		assert_eq!(u63::min_value().trailing_ones(), 0);
	}
	#[test]
	fn trailing_ones__some() {
		assert_eq!(u63::try_from(1).unwrap().trailing_ones(),      1);
		assert_eq!(u63::try_from(0b1010).unwrap().trailing_ones(), 0);
		assert_eq!((!(u63::max_value() << 2)).trailing_ones(),     2);
	}
	
	//		trailing_zeros														
	#[test]
	fn trailing_zeros__all() {
		assert_eq!(u63::min_value().trailing_zeros(), 63);
	}
	#[test]
	fn trailing_zeros__none() {
		assert_eq!(u63::max_value().trailing_zeros(), 0);
	}
	#[test]
	fn trailing_zeros__some() {
		assert_eq!(u63::try_from(1).unwrap().trailing_zeros(),      0);
		assert_eq!(u63::try_from(0b1010).unwrap().trailing_zeros(), 1);
		assert_eq!((u63::max_value() << 2).trailing_zeros(),        2);
	}
	
	//		wrapping_add														
	#[test]
	fn wrapping_add__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.wrapping_add(b), u63::try_from(8).unwrap());
	}
	#[test]
	fn wrapping_add__overflow_by_one() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.wrapping_add(b), u63::min_value());
	}
	#[test]
	fn wrapping_add__overflow_by_many() {
		let a = u63::try_from(i64::MAX as u64 - 1).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.wrapping_add(b), u63::try_from(1).unwrap());
	}
	
	//		wrapping_div														
	#[test]
	fn wrapping_div__normal() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.wrapping_div(b), u63::try_from(3).unwrap());
	}
	#[test]
	fn wrapping_div__by_zero() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(0).unwrap();
		assert_eq!(a.wrapping_div(b), u63::max_value());
	}
	
	//		wrapping_mul														
	#[test]
	fn wrapping_mul__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.wrapping_mul(b), u63::try_from(15).unwrap());
	}
	#[test]
	fn wrapping_mul__at_max() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.wrapping_mul(b), u63::max_value());
	}
	#[test]
	fn wrapping_mul__overflow_small() {
		let a = u63::max_value();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a.wrapping_mul(b), u63::max_value() - u63::try_from(1).unwrap());
	}
	#[test]
	fn wrapping_mul__overflow_large() {
		let a = u63::max_value();
		let b = u63::max_value();
		assert_eq!(a.wrapping_mul(b), u63::try_from(1).unwrap());
	}
	
	//		wrapping_pow														
	#[test]
	fn wrapping_pow__normal() {
		assert_eq!(u63::try_from(2).unwrap().wrapping_pow(3), u63::try_from(8).unwrap());
	}
	#[test]
	fn wrapping_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::try_from(2).unwrap().wrapping_pow(max_power), u63::try_from(1_u64 << max_power).unwrap());
	}
	#[test]
	fn wrapping_pow__overflow() {
		assert_eq!(u63::try_from(2).unwrap().wrapping_pow(63), u63::min_value());
	}
	#[test]
	fn wrapping_pow__zero() {
		let base = u63::try_from(0).unwrap();
		assert_eq!(base.wrapping_pow(0), u63::try_from(1).unwrap());
		assert_eq!(base.wrapping_pow(1), u63::try_from(0).unwrap());
	}
	
	//		wrapping_rem														
	#[test]
	fn wrapping_rem__normal() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(4).unwrap();
		assert_eq!(a.wrapping_rem(b), u63::try_from(3).unwrap());
	}
	#[test]
	fn wrapping_rem__by_zero() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(0).unwrap();
		assert_eq!(a.wrapping_rem(b), u63::max_value());
	}
	
	//		wrapping_sub														
	#[test]
	fn wrapping_sub__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::try_from(2).unwrap());
	}
	#[test]
	fn wrapping_sub__at_min() {
		let a = u63::try_from(1).unwrap();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::min_value());
	}
	#[test]
	fn wrapping_sub__underflow_by_one() {
		let a = u63::min_value();
		let b = u63::try_from(1).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::max_value());
	}
	#[test]
	fn wrapping_sub__underflow_by_many() {
		let a = u63::try_from(1).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::max_value() - u63::try_from(1).unwrap());
	}
	
	//		zero																
	#[test]
	fn zero() {
		assert_eq!(u63::zero(), u63::try_from(0).unwrap());
	}
}

mod derived_traits {
	use super::*;
	
	//		Debug																
	#[test]
	fn debug() {
		assert_eq!(format!("{:?}", u63::min_value()),           "Int::<63, false>(0)");
		assert_eq!(format!("{:?}", u63::try_from(42).unwrap()), "Int::<63, false>(42)");
		assert_eq!(format!("{:?}", u63::max_value()),           format!("Int::<63, false>({})", i64::MAX));
	}
	
	//		Default																
	#[test]
	fn default() {
		assert_eq!(u63::default(), u63::min_value());
	}
	
	//		Deserialize															
	#[test]
	fn deserialize() {
		assert_ok_eq!(serde_json::from_str::<u63>("42"), u63::try_from(42).unwrap());
	}
	
	//		Eq																	
	#[test]
	fn eq() {
		let a = u63::try_from(1).unwrap();
		let b = u63::try_from(2).unwrap();
		let c = u63::try_from(2).unwrap();
		
		assert_ne!(a, b);
		assert_eq!(b, c);
	}
	
	//		Hash																
	#[test]
	fn hash() {
		let mut set = HashSet::new();
		let a = u63::try_from(42).unwrap();
		let b = u63::try_from(42).unwrap();
		let c = u63::try_from(43).unwrap();
		
		_ = set.insert(a);
		assert!( set.contains(&b));
		assert!(!set.contains(&c));
	}
	
	//		Ord																	
	#[test]
	fn ord() {
		let a = u63::try_from(1).unwrap();
		let b = u63::try_from(2).unwrap();
		let c = u63::try_from(2).unwrap();
		
		assert!(a < b);
		assert!(b > a);
		assert!(b >= c);
		assert!(b <= c);
		assert_eq!(b.cmp(&c), Ordering::Equal);
	}
	
	//		Serialize															
	#[test]
	fn serialize() {
		assert_ok_eq!(serde_json::to_string(&u63::try_from(42).unwrap()), "42");
	}
}

mod traits {
	use super::*;
	
	//		Add																	
	#[test]
	fn add__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a + b, u63::try_from(8).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn add__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(1).unwrap();
		let _ = a + b;
	}
	
	//		AddAssign															
	#[test]
	fn add_assign__normal() {
		let mut a = u63::try_from(5).unwrap();
		let     b = u63::try_from(3).unwrap();
		a += b;
		assert_eq!(a, u63::try_from(8).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn add_assign__overflow() {
		let mut a = u63::max_value();
		let     b = u63::try_from(1).unwrap();
		a += b;
	}
	
	//		Binary																
	#[test]
	fn binary() {
		assert_eq!(format!("{:b}",  u63::try_from(42).unwrap()), "101010");
		assert_eq!(format!("{:#b}", u63::try_from(42).unwrap()), "0b101010");
	}
	
	//		BitAnd																
	#[test]
	fn bitand__normal() {
		let a = u63::try_from(0b1100).unwrap();
		let b = u63::try_from(0b1010).unwrap();
		assert_eq!(a & b, u63::try_from(0b1000).unwrap());
	}
	#[test]
	fn bitand__all_bits_set() {
		assert_eq!(u63::max_value() & u63::max_value(), u63::max_value());
	}
	#[test]
	fn bitand__zero_with_max() {
		assert_eq!(u63::min_value() & u63::max_value(), u63::min_value());
	}
	#[test]
	fn bitand__highest_valid_bit() {
		let high_bit = u63::try_from(1_u64 << 62).unwrap();
		assert_eq!(high_bit & u63::max_value(), high_bit);
	}
	
	//		BitAndAssign														
	#[test]
	fn bitand_assign__normal() {
		let mut a = u63::try_from(0b1100).unwrap();
		let     b = u63::try_from(0b1010).unwrap();
		a &= b;
		assert_eq!(a, u63::try_from(0b1000).unwrap());
	}
	#[test]
	fn bitand_assign__all_bits() {
		let mut a = u63::max_value();
		a &= u63::max_value();
		assert_eq!(a, u63::max_value());
	}
	#[test]
	fn bitand_assign__with_zero() {
		let mut a = u63::max_value();
		a &= u63::min_value();
		assert_eq!(a, u63::min_value());
	}
	
	//		BitOr																
	#[test]
	fn bitor__normal() {
		let a = u63::try_from(0b1100).unwrap();
		let b = u63::try_from(0b1010).unwrap();
		assert_eq!(a | b, u63::try_from(0b1110).unwrap());
	}
	#[test]
	fn bitor__with_zero() {
		let a = u63::try_from(0b1100).unwrap();
		assert_eq!(a | u63::min_value(), a);
	}
	#[test]
	fn bitor__with_max() {
		let a = u63::try_from(0b1100).unwrap();
		assert_eq!(a | u63::max_value(), u63::max_value());
	}
	
	//		BitOrAssign															
	#[test]
	fn bitor_assign__normal() {
		let mut a = u63::try_from(0b1100).unwrap();
		let     b = u63::try_from(0b1010).unwrap();
		a |= b;
		assert_eq!(a, u63::try_from(0b1110).unwrap());
	}
	#[test]
	fn bitor_assign__with_zero() {
		let mut a = u63::try_from(0b1100).unwrap();
		a |= u63::min_value();
		assert_eq!(a, u63::try_from(0b1100).unwrap());
	}
	#[test]
	fn bitor_assign__with_max() {
		let mut a = u63::try_from(0b1100).unwrap();
		a |= u63::max_value();
		assert_eq!(a, u63::max_value());
	}
	
	//		BitXor																
	#[test]
	fn bitxor__normal() {
		let a = u63::try_from(0b1100).unwrap();
		let b = u63::try_from(0b1010).unwrap();
		assert_eq!(a ^ b, u63::try_from(0b0110).unwrap());
	}
	#[test]
	fn bitxor__with_zero() {
		let a = u63::try_from(0b1100).unwrap();
		assert_eq!(a ^ u63::min_value(), a);
	}
	#[test]
	fn bitxor__with_max() {
		let a = u63::try_from(0b1100).unwrap();
		assert_eq!(a ^ u63::max_value(), !a & u63::max_value());
	}
	
	//		BitXorAssign														
	#[test]
	fn bitxor_assign__normal() {
		let mut a = u63::try_from(0b1100).unwrap();
		let     b = u63::try_from(0b1010).unwrap();
		a ^= b;
		assert_eq!(a, u63::try_from(0b0110).unwrap());
	}
	#[test]
	fn bitxor_assign__with_zero() {
		let mut a = u63::try_from(0b1100).unwrap();
		a ^= u63::min_value();
		assert_eq!(a, u63::try_from(0b1100).unwrap());
	}
	#[test]
	fn bitxor_assign__with_max() {
		let mut a = u63::try_from(0b1100).unwrap();
		a ^= u63::max_value();
		assert_eq!(a, !u63::try_from(0b1100).unwrap() & u63::max_value());
	}
	
	//		Display																
	#[test]
	fn display() {
		let value = u63::try_from(42).unwrap();
		assert_eq!(format!("{value}"), "42");
		assert_eq!(value.to_string(),  "42");
	}
	
	//		Div																	
	#[test]
	fn div__normal() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(2).unwrap();
		assert_eq!(a / b, u63::try_from(3).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to divide by zero")]
	fn div__by_zero() {
		let a = u63::try_from(6).unwrap();
		let b = u63::try_from(0).unwrap();
		let _ = a / b;
	}
	
	//		DivAssign															
	#[test]
	fn div_assign__normal() {
		let mut a = u63::try_from(6).unwrap();
		let     b = u63::try_from(2).unwrap();
		a /= b;
		assert_eq!(a, u63::try_from(3).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to divide by zero")]
	fn div_assign__by_zero() {
		let mut a = u63::try_from(6).unwrap();
		let     b = u63::try_from(0).unwrap();
		a /= b;
	}
	
	//		LowerHex															
	#[test]
	fn lowerhex() {
		assert_eq!(format!("{:x}",  u63::try_from(42).unwrap()), "2a");
		assert_eq!(format!("{:#x}", u63::try_from(42).unwrap()), "0x2a");
	}
	
	//		LowerExp															
	#[test]
	fn lowerexp() {
		assert_eq!(format!("{:e}", u63::try_from(42).unwrap()), "4.2e1");
		assert_eq!(format!("{:e}", u63::try_from(40).unwrap()), "4e1");
		assert_eq!(format!("{:e}", u63::min_value()),           "0e0");
		assert_eq!(format!("{:e}", u63::max_value()),           format!("{:e}", i64::MAX));
	}
	
	//		Mul																	
	#[test]
	fn mul__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a * b, u63::try_from(15).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn mul__overflow() {
		let a = u63::max_value();
		let b = u63::try_from(2).unwrap();
		let _ = a * b;
	}
	
	//		MulAssign															
	#[test]
	fn mul_assign__normal() {
		let mut a = u63::try_from(6).unwrap();
		let     b = u63::try_from(2).unwrap();
		a *= b;
		assert_eq!(a, u63::try_from(12).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn mul_assign__overflow() {
		let mut a = u63::max_value();
		let     b = u63::try_from(2).unwrap();
		a *= b;
	}
	
	//		Neg																	
	#[test]
	#[should_panic(expected = "Attempt to negate an unsigned value")]
	fn neg() {
		let value = u63::try_from(42).unwrap();
		let _     = -value;
	}
	
	//		Not																	
	#[test]
	fn not__zero() {
		assert_eq!(!u63::min_value(), u63::max_value());
	}
	#[test]
	fn not__max() {
		assert_eq!(!u63::max_value(), u63::min_value());
	}
	#[test]
	fn not__pattern() {
		assert_eq!(
			!u63::try_from(0b1010_u64).unwrap(),
			u63::try_from(0b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_0101_u64).unwrap()
		);
	}
	
	//		Octal																
	#[test]
	fn octal() {
		assert_eq!(format!("{:o}",  u63::try_from(42).unwrap()), "52");
		assert_eq!(format!("{:#o}", u63::try_from(42).unwrap()), "0o52");
		assert_eq!(format!("{:o}",  u63::min_value()),           "0");
		assert_eq!(format!("{:o}",  u63::max_value()),           format!("{:o}", i64::MAX));
	}
	
	//		Product																
	#[test]
	fn product__empty() {
		let values: Vec<u63> = vec![];
		assert_eq!(values.into_iter().product::<u63>(), u63::try_from(1).unwrap());
	}
	#[test]
	fn product__single() {
		let values = vec![
			u63::try_from(42).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::try_from(42).unwrap());
	}
	#[test]
	fn product__multiple_non_zero() {
		let values = vec![
			u63::try_from(2).unwrap(),
			u63::try_from(3).unwrap(),
			u63::try_from(4).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::try_from(24).unwrap());
	}
	#[test]
	fn product__multiple_with_zero() {
		let values = vec![
			u63::try_from(2).unwrap(),
			u63::try_from(0).unwrap(),
			u63::try_from(4).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::try_from(0).unwrap());
	}
	#[test]
	fn product__at_max() {
		let values = vec![
			u63::max_value(),
			u63::try_from(1).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::max_value());
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn product__overflow() {
		let values = vec![
			u63::max_value(),
			u63::try_from(2).unwrap(),
		];
		let _ = values.into_iter().product::<u63>();
	}
	
	//		Product<&>															
	#[test]
	fn product_ref__empty() {
		let values = [];
		assert_eq!(values.iter().product::<u63>(), u63::try_from(1).unwrap());
	}
	#[test]
	fn product_ref__single() {
		let values = [
			u63::try_from(42).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::try_from(42).unwrap());
	}
	#[test]
	fn product_ref__multiple_non_zero() {
		let values = [
			u63::try_from(2).unwrap(),
			u63::try_from(3).unwrap(),
			u63::try_from(4).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::try_from(24).unwrap());
	}
	#[test]
	fn product_ref__multiple_with_zero() {
		let values = [
			u63::try_from(2).unwrap(),
			u63::try_from(0).unwrap(),
			u63::try_from(4).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::try_from(0).unwrap());
	}
	#[test]
	fn product_ref__at_max() {
		let values = [
			u63::max_value(),
			u63::try_from(1).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::max_value());
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn product_ref__overflow() {
		let values = [
			u63::max_value(),
			u63::try_from(2).unwrap(),
		];
		let _ = values.iter().product::<u63>();
	}
	
	//		Rem																	
	#[test]
	fn rem__normal() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(4).unwrap();
		assert_eq!(a % b, u63::try_from(3).unwrap());
	}
	#[test]
	fn rem__zero() {
		let a = u63::try_from(8).unwrap();
		let b = u63::try_from(4).unwrap();
		assert_eq!(a % b, u63::try_from(0).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to calculate remainder with a divisor of zero")]
	fn rem__by_zero() {
		let a = u63::try_from(7).unwrap();
		let b = u63::try_from(0).unwrap();
		let _ = a % b;
	}
	
	//		RemAssign															
	#[test]
	fn rem_assign__normal() {
		let mut a = u63::try_from(7).unwrap();
		let     b = u63::try_from(4).unwrap();
		a %= b;
		assert_eq!(a, u63::try_from(3).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to calculate remainder with a divisor of zero")]
	fn rem_assign__by_zero() {
		let mut a = u63::try_from(7).unwrap();
		let     b = u63::try_from(0).unwrap();
		a %= b;
	}
	
	//		Shl																	
	#[test]
	fn shl__normal() {
		assert_eq!(u63::try_from(0b1  ).unwrap() << 3, u63::try_from(0b1000 ).unwrap());
		assert_eq!(u63::try_from(0b101).unwrap() << 2, u63::try_from(0b10100).unwrap());
	}
	#[test]
	fn shl__zero_shift() {
		let value = u63::try_from(42).unwrap();
		assert_eq!(value << 0, value);
	}
	#[test]
	fn shl__overflow() {
		assert_eq!(u63::try_from(1).unwrap() << 63, u63::min_value());
		assert_eq!(u63::max_value()          << 1,  u63::max_value() >> 1 << 1);
	}
	#[test]
	fn shl__large_shift() {
		assert_eq!(u63::try_from(1).unwrap() << 65, u63::try_from(2).unwrap());
	}
	
	//		ShlAssign															
	#[test]
	fn shl_assign() {
		let mut value = u63::try_from(0b1).unwrap();
		value <<= 3;
		assert_eq!(value, u63::try_from(0b1000).unwrap());
	}
	
	//		Shr																	
	#[test]
	fn shr__normal() {
		assert_eq!(u63::try_from(0b1000 ).unwrap() >> 3, u63::try_from(0b1  ).unwrap());
		assert_eq!(u63::try_from(0b10100).unwrap() >> 2, u63::try_from(0b101).unwrap());
	}
	#[test]
	fn shr__zero_shift() {
		let value = u63::try_from(42).unwrap();
		assert_eq!(value >> 0, value);
	}
	#[test]
	fn shr__underflow() {
		assert_eq!(u63::try_from(1).unwrap() >> 63, u63::min_value());
		assert_eq!(u63::max_value()          >> 62, u63::try_from(1).unwrap());
		assert_eq!(u63::max_value()          >> 63, u63::min_value());
	}
	#[test]
	fn shr__large_shift() {
		assert_eq!(u63::try_from(0b1000).unwrap() >> 65, u63::try_from(0b0100).unwrap());
	}
	
	//		ShrAssign															
	#[test]
	fn shr_assign() {
		let mut value = u63::try_from(0b1000).unwrap();
		value >>= 3;
		assert_eq!(value, u63::try_from(0b1).unwrap());
	}
	
	//		Sub																	
	#[test]
	fn sub__normal() {
		let a = u63::try_from(5).unwrap();
		let b = u63::try_from(3).unwrap();
		assert_eq!(a - b, u63::try_from(2).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to subtract overflowed")]
	fn sub__underflow() {
		let a = u63::min_value();
		let b = u63::try_from(1).unwrap();
		let _ = a - b;
	}
	
	//		SubAssign															
	#[test]
	fn sub_assign__normal() {
		let mut a = u63::try_from(5).unwrap();
		let     b = u63::try_from(3).unwrap();
		a -= b;
		assert_eq!(a, u63::try_from(2).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to subtract overflowed")]
	fn sub_assign__underflow() {
		let mut a = u63::min_value();
		let     b = u63::try_from(1).unwrap();
		a -= b;
	}
	
	//		Sum																	
	#[test]
	fn sum__empty() {
		let values: Vec<u63> = vec![];
		assert_eq!(values.into_iter().sum::<u63>(), u63::try_from(0).unwrap());
	}
	#[test]
	fn sum__single() {
		let values = vec![
			u63::try_from(42).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::try_from(42).unwrap());
	}
	#[test]
	fn sum__multiple_non_zero() {
		let values = vec![
			u63::try_from(1).unwrap(),
			u63::try_from(2).unwrap(),
			u63::try_from(3).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::try_from(6).unwrap());
	}
	#[test]
	fn sum__multiple_with_zero() {
		let values = vec![
			u63::try_from(1).unwrap(),
			u63::try_from(0).unwrap(),
			u63::try_from(3).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::try_from(4).unwrap());
	}
	#[test]
	fn sum__at_max() {
		let values = vec![
			u63::max_value() - u63::try_from(1).unwrap(),
			u63::try_from(1).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::max_value());
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn sum__overflow() {
		let values = vec![
			u63::max_value(),
			u63::try_from(1).unwrap(),
		];
		let _ = values.into_iter().sum::<u63>();
	}
	
	//		Sum<&>																
	#[test]
	fn sum_ref__empty() {
		let values = [];
		assert_eq!(values.iter().sum::<u63>(), u63::try_from(0).unwrap());
	}
	#[test]
	fn sum_ref__single() {
		let values = [
			u63::try_from(42).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::try_from(42).unwrap());
	}
	#[test]
	fn sum_ref__multiple_non_zero() {
		let values = [
			u63::try_from(1).unwrap(),
			u63::try_from(2).unwrap(),
			u63::try_from(3).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::try_from(6).unwrap());
	}
	#[test]
	fn sum_ref__multiple_with_zero() {
		let values = [
			u63::try_from(1).unwrap(),
			u63::try_from(0).unwrap(),
			u63::try_from(3).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::try_from(4).unwrap());
	}
	#[test]
	fn sum_ref__at_max() {
		let values = [
			u63::max_value() - u63::try_from(1).unwrap(),
			u63::try_from(1).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::max_value());
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn sum_ref__overflow() {
		let values = [
			u63::max_value(),
			u63::try_from(1).unwrap(),
		];
		let _ = values.iter().sum::<u63>();
	}
	
	//		UpperExp															
	#[test]
	fn upperexp() {
		assert_eq!(format!("{:E}", u63::try_from(42).unwrap()), "4.2E1");
		assert_eq!(format!("{:E}", u63::try_from(40).unwrap()), "4E1");
		assert_eq!(format!("{:E}", u63::min_value()),           "0E0");
		assert_eq!(format!("{:E}", u63::max_value()),           format!("{:E}", i64::MAX));
	}
	
	//		UpperHex															
	#[test]
	fn upperhex() {
		assert_eq!(format!("{:X}",  u63::try_from(42).unwrap()), "2A");
		assert_eq!(format!("{:#X}", u63::try_from(42).unwrap()), "0x2A");
	}
}

mod conversions {
	use super::*;
	
	//		FromSql																
	#[test]
	fn from_sql__i32() {
		assert_ok_eq!(u63::from_sql(&Type::INT4, &42_i32.to_be_bytes()), u63::try_from(42).unwrap());
	}
	#[test]
	fn from_sql__i64() {
		assert_ok_eq!(u63::from_sql(&Type::INT8, &42_i64.to_be_bytes()), u63::try_from(42).unwrap());
	}
	#[test]
	fn from_sql__invalid_type() {
		let err = u63::from_sql(&Type::FLOAT4, &42_i32.to_be_bytes());
		assert_err!(&err);
		assert_eq!(err.unwrap_err().to_string(), "Invalid type for Int<63, false>: float4");
	}
	#[test]
	fn from_sql__negative() {
		let err = u63::from_sql(&Type::INT8, &(-1_i64).to_be_bytes());
		assert_err!(&err);
		assert_eq!(err.unwrap_err().to_string(), "Value is negative");
	}
	#[test]
	fn from_sql__accepts() {
		assert!( <u63 as FromSql>::accepts(&Type::INT4));
		assert!( <u63 as FromSql>::accepts(&Type::INT8));
		assert!( <u63 as FromSql>::accepts(&Type::TEXT));
		assert!(!<u63 as FromSql>::accepts(&Type::FLOAT4));
	}
	
	//		FromStr																
	#[test]
	fn from_str__valid() {
		assert_ok_eq!( "0".parse::<u63>(),                 u63::min_value());
		assert_ok_eq!("42".parse::<u63>(),                 u63::try_from(42).unwrap());
		assert_ok_eq!(i64::MAX.to_string().parse::<u63>(), u63::max_value());
	}
	#[test]
	fn from_str__invalid_format() {
		let err1 = "abc".parse::<u63>();
		assert_err_eq!(&err1, &ConversionError::InvalidRadix('a', 10));
		assert_eq!(err1.unwrap_err().to_string(), s!("Invalid digit for base 10: a"));
		
		let err2 = "12.34".parse::<u63>();
		assert_err_eq!(&err2, &ConversionError::InvalidDigit('.'));
		assert_eq!(err2.unwrap_err().to_string(), s!("Invalid digit: ."));
	}
	#[test]
	fn from_str__too_large() {
		assert_err_eq!(u64::MAX.to_string().parse::<u63>(), ConversionError::ValueTooLarge);
	}
	
	//		ToSql																
	#[test]
	fn to_sql__valid() {
		let mut bytes = BytesMut::new();
		
		//	Match on IsNull variant
		match u63::try_from(42).unwrap().to_sql(&Type::INT8, &mut bytes).unwrap() {
			IsNull::No  => (),  //  Expected case
			IsNull::Yes => panic!("Unexpected NULL value"),
		}
		
		//	Convert BytesMut to i64 and verify
		assert_eq!(i64::from_be_bytes(bytes.as_ref().try_into().unwrap()), 42_i64);
	}
	#[test]
	fn to_sql__accepts() {
		assert!( <u63 as FromSql>::accepts(&Type::INT4));
		assert!( <u63 as FromSql>::accepts(&Type::INT8));
		assert!( <u63 as FromSql>::accepts(&Type::TEXT));
		assert!(!<u63 as FromSql>::accepts(&Type::FLOAT4));
	}
	
	//		TryFrom: i8 -> u63													
	#[test]
	fn try_from__i8__valid() {
		assert_ok_eq!(u63::try_from( 0_i8),   u63::min_value());
		assert_ok_eq!(u63::try_from(42_i8),   u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(i8::MAX), u63::try_from(i8::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i8__negative() {
		assert_err_eq!(u63::try_from(-1_i8),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i8::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i16 -> u63													
	#[test]
	fn try_from__i16__valid() {
		assert_ok_eq!(u63::try_from( 0_i16),   u63::min_value());
		assert_ok_eq!(u63::try_from(42_i16),   u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(i16::MAX), u63::try_from(i16::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i16__negative() {
		assert_err_eq!(u63::try_from(-1_i16),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i16::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i32 -> u63													
	#[test]
	fn try_from__i32__valid() {
		assert_ok_eq!(u63::try_from( 0_i32),   u63::min_value());
		assert_ok_eq!(u63::try_from(42_i32),   u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(i32::MAX), u63::try_from(i32::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i32__negative() {
		assert_err_eq!(u63::try_from(-1_i32),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i32::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i64 -> u63													
	#[test]
	fn try_from__i64__valid() {
		assert_ok_eq!(u63::try_from( 0_i64),   u63::min_value());
		assert_ok_eq!(u63::try_from(42_i64),   u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(i32::MAX), u63::try_from(i32::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i64__negative() {
		assert_err_eq!(u63::try_from(-1_i64),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i64::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i128 -> u63												
	#[test]
	fn try_from__i128__valid() {
		assert_ok_eq!(u63::try_from( 0_i128),          u63::min_value());
		assert_ok_eq!(u63::try_from(42_i128),          u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(i64::MAX as i128), u63::max_value());
	}
	#[test]
	fn try_from__i128__negative() {
		assert_err_eq!(u63::try_from(-1_i128),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i128::MIN), ConversionError::ValueIsNegative);
	}
	#[test]
	fn try_from__i128__too_large() {
		assert_err_eq!(u63::try_from(i64::MAX as i128 + 1), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: isize -> u63												
	#[test]
	fn try_from__isize__valid() {
		assert_ok_eq!(u63::try_from( 0_isize),   u63::min_value());
		assert_ok_eq!(u63::try_from(42_isize),   u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(isize::MAX), u63::try_from(isize::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__isize__negative() {
		assert_err_eq!(u63::try_from(-1_isize),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(isize::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: u8 -> u63													
	#[test]
	fn try_from__u8() {
		assert_ok_eq!(u63::try_from(42_u8), u63::try_from(42).unwrap());
	}
	
	//		TryFrom: u16 -> u63													
	#[test]
	fn try_from__u16() {
		assert_ok_eq!(u63::try_from(0_u16),    u63::min_value());
		assert_ok_eq!(u63::try_from(42_u16),   u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(u16::MAX), u63::try_from(u16::MAX as u64).unwrap());
	}
	
	//		TryFrom: u32 -> u63													
	#[test]
	fn try_from__u32() {
		assert_ok_eq!(u63::try_from(0_u32),    u63::min_value());
		assert_ok_eq!(u63::try_from(42_u32),   u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(u32::MAX), u63::try_from(u32::MAX as u64).unwrap());
	}
	
	//		TryFrom: u63 -> i8													
	#[test]
	fn try_from__to_i8__valid() {
		assert_ok_eq!(i8::try_from(u63::min_value()),                       0_i8);
		assert_ok_eq!(i8::try_from(u63::try_from(42).unwrap()),             42_i8);
		assert_ok_eq!(i8::try_from(u63::try_from(i8::MAX as u64).unwrap()), i8::MAX);
	}
	#[test]
	fn try_from__to_i8__too_large() {
		assert_err_eq!(i8::try_from(u63::try_from(i8::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> i16													
	#[test]
	fn try_from__to_i16__valid() {
		assert_ok_eq!(i16::try_from(u63::min_value()),                        0_i16);
		assert_ok_eq!(i16::try_from(u63::try_from(42).unwrap()),              42_i16);
		assert_ok_eq!(i16::try_from(u63::try_from(i16::MAX as u64).unwrap()), i16::MAX);
	}
	#[test]
	fn try_from__to_i16__too_large() {
		assert_err_eq!(i16::try_from(u63::try_from(i16::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> i32													
	#[test]
	fn try_from__to_i32__valid() {
		assert_ok_eq!(i32::try_from(u63::min_value()),                        0_i32);
		assert_ok_eq!(i32::try_from(u63::try_from(42).unwrap()),              42_i32);
		assert_ok_eq!(i32::try_from(u63::try_from(i32::MAX as u64).unwrap()), i32::MAX);
	}
	#[test]
	fn try_from__to_i32__too_large() {
		assert_err_eq!(i32::try_from(u63::try_from(i32::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> i64													
	#[test]
	fn try_from__to_i64() {
		assert_ok_eq!(i64::try_from(u63::min_value()),           0_i64);
		assert_ok_eq!(i64::try_from(u63::try_from(42).unwrap()), 42_i64);
		assert_ok_eq!(i64::try_from(u63::max_value()),           i64::MAX);
	}
	
	//		TryFrom: u63 -> i128												
	#[test]
	fn tryfrom__to_i128() {
		assert_ok_eq!(i128::try_from(u63::min_value()),           0_i128);
		assert_ok_eq!(i128::try_from(u63::try_from(42).unwrap()), 42_i128);
		assert_ok_eq!(i128::try_from(u63::max_value()),           i64::MAX as i128);
	}
	
	//		TryFrom: u63 -> isize												
	#[test]
	fn try_from__to_isize__valid() {
		assert_ok_eq!(isize::try_from(u63::min_value()),                          0_isize);
		assert_ok_eq!(isize::try_from(u63::try_from(42).unwrap()),                42_isize);
		assert_ok_eq!(isize::try_from(u63::try_from(isize::MAX as u64).unwrap()), isize::MAX);
	}
	#[test]
	fn try_from__to_isize__too_large() {
		//	Only test on 32-bit platforms where isize::MAX < u63::max_value()
		if (isize::MAX as u64) < u64::try_from(u63::max_value()).unwrap() {
			assert_err_eq!(
				isize::try_from(u63::try_from(isize::MAX as u64 + 1).unwrap()),
				ConversionError::ValueTooLarge
			);
		}
	}
	
	//		TryFrom: u63 -> u8													
	#[test]
	fn try_from__to_u8__valid() {
		assert_ok_eq!(u8::try_from(u63::min_value()),                       0_u8);
		assert_ok_eq!(u8::try_from(u63::try_from(42).unwrap()),             42_u8);
		assert_ok_eq!(u8::try_from(u63::try_from(u8::MAX as u64).unwrap()), u8::MAX);
	}
	#[test]
	fn try_from__to_u8__too_large() {
		assert_err_eq!(u8::try_from(u63::try_from(u8::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> u16													
	#[test]
	fn try_from__to_u16__valid() {
		assert_ok_eq!(u16::try_from(u63::min_value()),                        0_u16);
		assert_ok_eq!(u16::try_from(u63::try_from(42).unwrap()),              42_u16);
		assert_ok_eq!(u16::try_from(u63::try_from(u16::MAX as u64).unwrap()), u16::MAX);
	}
	#[test]
	fn try_from__to_u16__too_large() {
		assert_err_eq!(u16::try_from(u63::try_from(u16::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> u32													
	#[test]
	fn try_from__to_u32__valid() {
		assert_ok_eq!(u32::try_from(u63::min_value()),                        0_u32);
		assert_ok_eq!(u32::try_from(u63::try_from(42).unwrap()),              42_u32);
		assert_ok_eq!(u32::try_from(u63::try_from(u32::MAX as u64).unwrap()), u32::MAX);
	}
	#[test]
	fn try_from__to_u32__too_large() {
		assert_err_eq!(u32::try_from(u63::try_from(u32::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> u64													
	#[test]
	fn tryfrom__to_u64() {
		assert_ok_eq!(u64::try_from(u63::min_value()),           0_u64);
		assert_ok_eq!(u64::try_from(u63::try_from(42).unwrap()), 42_u64);
		assert_ok_eq!(u64::try_from(u63::max_value()),           i64::MAX as u64);
	}
	
	//		TryFrom: u63 -> u128												
	#[test]
	fn tryfrom__to_u128() {
		assert_ok_eq!(u128::try_from(u63::min_value()),           0_u128);
		assert_ok_eq!(u128::try_from(u63::try_from(42).unwrap()), 42_u128);
		assert_ok_eq!(u128::try_from(u63::max_value()),           i64::MAX as u128);
	}
	
	//		TryFrom: u63 -> usize												
	#[test]
	fn try_from__to_usize__valid() {
		assert_ok_eq!(usize::try_from(u63::min_value()),           0_usize);
		assert_ok_eq!(usize::try_from(u63::try_from(42).unwrap()), 42_usize);
	}
	#[test]
	fn try_from__to_usize__too_large() {
		//	Only test on 32-bit platforms where usize::MAX < u63::max_value()
		if (usize::MAX as u64) < u64::try_from(u63::max_value()).unwrap() {
			//	Use a value definitely larger than usize::MAX but within u63 range
			let large_value = u63::try_from(usize::MAX as u64).unwrap() + u63::try_from(1).unwrap();
			assert_err_eq!(
				usize::try_from(large_value),
				ConversionError::ValueTooLarge
			);
		}
	}
	
	//		TryFrom: u64 -> u63													
	#[test]
	fn try_from__u64__valid() {
		assert_ok_eq!(u63::try_from( 0_u64),          u63::min_value());
		assert_ok_eq!(u63::try_from(42_u64),          u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(i64::MAX as u64), u63::max_value());
	}
	#[test]
	fn try_from__u64__too_large() {
		assert_err_eq!(u63::try_from(i64::MAX as u64 + 1), ConversionError::ValueTooLarge);
		assert_err_eq!(u63::try_from(u64::MAX),            ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u128 -> u63												
	#[test]
	fn try_from__u128__valid() {
		assert_ok_eq!(u63::try_from( 0_u128),          u63::min_value());
		assert_ok_eq!(u63::try_from(42_u128),          u63::try_from(42).unwrap());
		assert_ok_eq!(u63::try_from(i64::MAX as u128), u63::max_value());
	}
	#[test]
	fn try_from__u128__too_large() {
		assert_err_eq!(u63::try_from(i64::MAX as u128 + 1), ConversionError::ValueTooLarge);
		assert_err_eq!(u63::try_from(u128::MAX),            ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: usize -> u63												
	#[test]
	fn try_from__usize__valid() {
		assert_ok_eq!(u63::try_from( 0_usize), u63::min_value());
		assert_ok_eq!(u63::try_from(42_usize), u63::try_from(42).unwrap());
		//	Can't test MAX as it varies by platform
	}
	#[test]
	fn try_from__usize__too_large() {
		//	Only test if usize::MAX > u63::max_value() (64-bit platforms)
		if usize::MAX as u64 > u64::try_from(u63::max_value()).unwrap() {
			assert_err_eq!(
				u63::try_from(usize::try_from(u64::try_from(u63::max_value()).unwrap()).unwrap() + 1),
				ConversionError::ValueTooLarge
			);
		}
	}
}


