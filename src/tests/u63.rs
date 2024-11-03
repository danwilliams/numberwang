//		Packages

use super::*;
use bytes::BytesMut;
use claims::{assert_err, assert_err_eq, assert_ok_eq};
use core::cmp::Ordering;
use rubedo::sugar::s;
use std::collections::HashSet;
use tokio_postgres::types::{Type, IsNull};



//		Tests

mod constructors {
	use super::*;
	
	//		new																	
	#[test]
	fn new__valid() {
		assert_ok_eq!(u63::new(0), u63::MIN);
		assert_ok_eq!(u63::new(i64::MAX as u64), u63::MAX);
	}
	#[test]
	fn new__invalid() {
		let err1 = u63::new(u64::MAX);
		assert_err_eq!(&err1, &ConversionError::ValueTooLarge);
		assert_eq!(err1.unwrap_err().to_string(), s!("Value too large"));
		
		let err2 = u63::new(i64::MAX as u64 + 1);
		assert_err_eq!(&err2, &ConversionError::ValueTooLarge);
		assert_eq!(err2.unwrap_err().to_string(), s!("Value too large"));
	}
}

mod public_methods {
	use super::*;
	
	//		as_u64																
	#[test]
	fn as_u64__min() {
		assert_eq!(u63::MIN.as_u64(), 0);
	}
	#[test]
	fn as_u64__normal() {
		assert_eq!(u63::new(42).unwrap().as_u64(), 42);
	}
	#[test]
	fn as_u64__max() {
		assert_eq!(u63::MAX.as_u64(), i64::MAX as u64);
	}
	
	//		as_i64																
	#[test]
	fn as_i64__min() {
		assert_eq!(u63::MIN.as_i64(), 0);
	}
	#[test]
	fn as_i64__normal() {
		assert_eq!(u63::new(42).unwrap().as_i64(), 42);
	}
	#[test]
	fn as_i64__max() {
		assert_eq!(u63::MAX.as_i64(), i64::MAX);
	}
	
	//		checked_add															
	#[test]
	fn checked_add__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.checked_add(b), Some(u63::new(8).unwrap()));
	}
	#[test]
	fn checked_add__at_max() {
		let a = u63::new(i64::MAX as u64 - 1).unwrap();
		let b = u63::new(1).unwrap();
		assert_eq!(a.checked_add(b), Some(u63::MAX));
	}
	#[test]
	fn checked_add__overflow() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.checked_add(b), None);
	}
	
	//		checked_div															
	#[test]
	fn checked_div__normal() {
		let a = u63::new(6).unwrap();
		let b = u63::new(2).unwrap();
		assert_eq!(a.checked_div(b), Some(u63::new(3).unwrap()));
	}
	#[test]
	fn checked_div__by_zero() {
		let a = u63::new(6).unwrap();
		let b = u63::new(0).unwrap();
		assert_eq!(a.checked_div(b), None);
	}
	
	//		checked_mul															
	#[test]
	fn checked_mul__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.checked_mul(b), Some(u63::new(15).unwrap()));
	}
	#[test]
	fn checked_mul__at_max() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.checked_mul(b), Some(u63::MAX));
	}
	#[test]
	fn checked_mul__overflow() {
		let a = u63::MAX;
		let b = u63::new(2).unwrap();
		assert_eq!(a.checked_mul(b), None);
	}
	
	//		checked_pow															
	#[test]
	fn checked_pow__normal() {
		assert_eq!(u63::new(2).unwrap().checked_pow(3), Some(u63::new(8).unwrap()));
	}
	#[test]
	fn checked_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::new(2).unwrap().checked_pow(max_power), Some(u63::new(1_u64 << max_power).unwrap()));
	}
	#[test]
	fn checked_pow__overflow() {
		assert_eq!(u63::new(2).unwrap().checked_pow(63), None);
	}
	#[test]
	fn checked_pow__zero() {
		let base = u63::new(0).unwrap();
		assert_eq!(base.checked_pow(0), Some(u63::new(1).unwrap()));
		assert_eq!(base.checked_pow(1), Some(u63::new(0).unwrap()));
	}
	
	//		checked_rem															
	#[test]
	fn checked_rem__normal() {
		let a = u63::new(7).unwrap();
		let b = u63::new(4).unwrap();
		assert_eq!(a.checked_rem(b), Some(u63::new(3).unwrap()));
	}
	#[test]
	fn checked_rem__by_zero() {
		let a = u63::new(7).unwrap();
		let b = u63::new(0).unwrap();
		assert_eq!(a.checked_rem(b), None);
	}
	
	//		checked_sub															
	#[test]
	fn checked_sub__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.checked_sub(b), Some(u63::new(2).unwrap()));
	}
	#[test]
	fn checked_sub__at_min() {
		let a = u63::new(1).unwrap();
		let b = u63::new(1).unwrap();
		assert_eq!(a.checked_sub(b), Some(u63::MIN));
	}
	#[test]
	fn checked_sub__underflow() {
		let a = u63::MIN;
		let b = u63::new(1).unwrap();
		assert_eq!(a.checked_sub(b), None);
	}
	
	//		count_ones															
	#[test]
	fn count_ones__zero() {
		assert_eq!(u63::MIN.count_ones(), 0);
	}
	#[test]
	fn count_ones__one() {
		assert_eq!(u63::new(1).unwrap().count_ones(), 1);
	}
	#[test]
	fn count_ones__some() {
		assert_eq!(u63::new(0b1010_1010).unwrap().count_ones(), 4);
	}
	#[test]
	fn count_ones__all() {
		assert_eq!(u63::MAX.count_ones(), 63);
	}
	
	//		count_zeroes														
	#[test]
	fn count_zeros__zero() {
		assert_eq!(u63::MAX.count_zeros(), 0);
	}
	#[test]
	fn count_zeros__one() {
		assert_eq!(u63::new(i64::MAX as u64 - 1).unwrap().count_zeros(), 1);
	}
	#[test]
	fn count_zeros__some() {
		//	63 - 4 ones
		assert_eq!(u63::new(0b1010_1010).unwrap().count_zeros(), 59);
	}
	#[test]
	fn count_zeros__all() {
		//	One less than u64 due to highest bit
		assert_eq!(u63::MIN.count_zeros(), 63);
	}
	
	//		is_power_of_two														
	#[test]
	fn is_power_of_two__zero() {
		assert!(!u63::MIN.is_power_of_two());
	}
	#[test]
	fn is_power_of_two__one() {
		assert!(u63::new(1).unwrap().is_power_of_two());
	}
	#[test]
	fn is_power_of_two__two() {
		assert!(u63::new(2).unwrap().is_power_of_two());
	}
	#[test]
	fn is_power_of_two__not_power() {
		assert!(!u63::new(42).unwrap().is_power_of_two());
	}
	#[test]
	fn is_power_of_two__highest() {
		assert!(u63::new(1 << 62).unwrap().is_power_of_two());
	}
	
	//		leading_ones														
	#[test]
	fn leading_ones__all() {
		assert_eq!(u63::MAX.leading_ones(), 63);
	}
	#[test]
	fn leading_ones__none() {
		assert_eq!(u63::MIN.leading_ones(), 0);
	}
	#[test]
	fn leading_ones__some() {
		assert_eq!(u63::new(1).unwrap().leading_ones(),      0);
		assert_eq!(u63::new(0b1010).unwrap().leading_ones(), 0);
		assert_eq!((!(u63::MAX >> 2)).leading_ones(),        2);
	}
	
	//		leading_zeros														
	#[test]
	fn leading_zeros__all() {
		assert_eq!(u63::MIN.leading_zeros(), 63);
	}
	#[test]
	fn leading_zeros__none() {
		assert_eq!(u63::MAX.leading_zeros(), 0);
	}
	#[test]
	fn leading_zeros__some() {
		assert_eq!(u63::new(1).unwrap().leading_zeros(),      62);
		assert_eq!(u63::new(0b1010).unwrap().leading_zeros(), 59);
		assert_eq!((u63::MAX >> 2).leading_zeros(),           2);
	}
	
	//		overflowing_add														
	#[test]
	fn overflowing_add__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.overflowing_add(b), (u63::new(8).unwrap(), false));
	}
	#[test]
	fn overflowing_add__at_max() {
		let a = u63::new(i64::MAX as u64 - 1).unwrap();
		let b = u63::new(1).unwrap();
		assert_eq!(a.overflowing_add(b), (u63::MAX, false));
	}
	#[test]
	fn overflowing_add__overflow() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.overflowing_add(b), (u63::MIN, true));
	}
	
	//		overflowing_div														
	#[test]
	fn overflowing_div__normal() {
		let a = u63::new(6).unwrap();
		let b = u63::new(2).unwrap();
		assert_eq!(a.overflowing_div(b), (u63::new(3).unwrap(), false));
	}
	#[test]
	fn overflowing_div__by_zero() {
		let a = u63::new(6).unwrap();
		let b = u63::new(0).unwrap();
		assert_eq!(a.overflowing_div(b), (u63::MAX, true));
	}
	
	//		overflowing_mul														
	#[test]
	fn overflowing_mul__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.overflowing_mul(b), (u63::new(15).unwrap(), false));
	}
	#[test]
	fn overflowing_mul__at_max() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.overflowing_mul(b), (u63::MAX, false));
	}
	#[test]
	fn overflowing_mul__overflow() {
		let a = u63::MAX;
		let b = u63::new(2).unwrap();
		assert_eq!(a.overflowing_mul(b), (u63::MAX - u63::new(1).unwrap(), true));
	}
	
	//		overflowing_pow														
	#[test]
	fn overflowing_pow__normal() {
		assert_eq!(u63::new(2).unwrap().overflowing_pow(3), (u63::new(8).unwrap(), false));
	}
	#[test]
	fn overflowing_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::new(2).unwrap().overflowing_pow(max_power), (u63::new(1_u64 << max_power).unwrap(), false));
	}
	#[test]
	fn overflowing_pow__overflow() {
		assert_eq!(u63::new(2).unwrap().overflowing_pow(63), (u63::MIN, true));
	}
	
	//		overflowing_rem														
	#[test]
	fn overflowing_rem__normal() {
		let a = u63::new(7).unwrap();
		let b = u63::new(4).unwrap();
		assert_eq!(a.overflowing_rem(b), (u63::new(3).unwrap(), false));
	}
	#[test]
	fn overflowing_rem__by_zero() {
		let a = u63::new(7).unwrap();
		let b = u63::new(0).unwrap();
		assert_eq!(a.overflowing_rem(b), (u63::MAX, true));
	}
	
	//		overflowing_sub														
	#[test]
	fn overflowing_sub__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.overflowing_sub(b), (u63::new(2).unwrap(), false));
	}
	#[test]
	fn overflowing_sub__at_min() {
		let a = u63::new(1).unwrap();
		let b = u63::new(1).unwrap();
		assert_eq!(a.overflowing_sub(b), (u63::MIN, false));
	}
	#[test]
	fn overflowing_sub__underflow() {
		let a = u63::MIN;
		let b = u63::new(1).unwrap();
		assert_eq!(a.overflowing_sub(b), (u63::MAX, true));
	}
	
	//		reverse_bits														
	#[test]
	fn reverse_bits__zero() {
		assert_eq!(u63::MIN.reverse_bits(), u63::MIN);
	}
	#[test]
	fn reverse_bits__one() {
		assert_eq!(u63::new(1).unwrap().reverse_bits(), u63::new(1 << 62).unwrap());
	}
	#[test]
	fn reverse_bits__pattern() {
		assert_eq!(
			u63::new(0b1010).unwrap().reverse_bits(),
			u63::new(0b0010_1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000).unwrap()
		);
	}
	#[test]
	fn reverse_bits__all() {
		assert_eq!(u63::MAX.reverse_bits(), u63::MAX);
	}
	
	//		rotate_left															
	#[test]
	fn rotate_left__zero() {
		let value = u63::new(0b1).unwrap();
		assert_eq!(value.rotate_left(0), value);
	}
	#[test]
	fn rotate_left__one() {
		assert_eq!(u63::new(0b1).unwrap().rotate_left(1), u63::new(0b10).unwrap());
	}
	#[test]
	fn rotate_left__many() {
		assert_eq!(u63::new(0b1).unwrap().rotate_left(4), u63::new(0b10000).unwrap());
	}
	#[test]
	fn rotate_left__full_rotation() {
		let value = u63::new(0b1).unwrap();
		assert_eq!(value.rotate_left(63), value);
	}
	
	//		rotate_right														
	#[test]
	fn rotate_right__zero() {
		let value = u63::new(0b1000).unwrap();
		assert_eq!(value.rotate_right(0), value);
	}
	#[test]
	fn rotate_right__one() {
		assert_eq!(u63::new(0b1000).unwrap().rotate_right(1), u63::new(0b100).unwrap());
	}
	#[test]
	fn rotate_right__many() {
		assert_eq!(u63::new(0b1000).unwrap().rotate_right(2), u63::new(0b10).unwrap());
	}
	#[test]
	fn rotate_right__full_rotation() {
		let value = u63::new(0b1000).unwrap();
		assert_eq!(value.rotate_right(63), value);
	}
	
	//		saturating_add														
	#[test]
	fn saturating_add__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.saturating_add(b), u63::new(8).unwrap());
	}
	#[test]
	fn saturating_add__at_max() {
		let a = u63::new(i64::MAX as u64 - 1).unwrap();
		let b = u63::new(1).unwrap();
		assert_eq!(a.saturating_add(b), u63::MAX);
	}
	#[test]
	fn saturating_add__overflow() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.saturating_add(b), u63::MAX);
	}
	
	//		saturating_div														
	#[test]
	fn saturating_div__normal() {
		let a = u63::new(6).unwrap();
		let b = u63::new(2).unwrap();
		assert_eq!(a.saturating_div(b), u63::new(3).unwrap());
	}
	#[test]
	fn saturating_div__by_zero() {
		let a = u63::new(6).unwrap();
		let b = u63::new(0).unwrap();
		assert_eq!(a.saturating_div(b), u63::MAX);
	}
	
	//		saturating_mul														
	#[test]
	fn saturating_mul__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.saturating_mul(b), u63::new(15).unwrap());
	}
	#[test]
	fn saturating_mul__at_max() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.saturating_mul(b), u63::MAX);
	}
	#[test]
	fn saturating_mul__overflow() {
		let a = u63::MAX;
		let b = u63::new(2).unwrap();
		assert_eq!(a.saturating_mul(b), u63::MAX);
	}
	
	//		saturating_pow														
	#[test]
	fn saturating_pow__normal() {
		assert_eq!(u63::new(2).unwrap().saturating_pow(3), u63::new(8).unwrap());
	}
	#[test]
	fn saturating_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::new(2).unwrap().saturating_pow(max_power), u63::new(1_u64 << max_power).unwrap());
	}
	#[test]
	fn saturating_pow__overflow() {
		assert_eq!(u63::new(2).unwrap().saturating_pow(63), u63::MAX);
	}
	#[test]
	fn saturating_pow__zero() {
		let base = u63::new(0).unwrap();
		assert_eq!(base.saturating_pow(0), u63::new(1).unwrap());
		assert_eq!(base.saturating_pow(1), u63::new(0).unwrap());
	}
	
	//		saturating_sub														
	#[test]
	fn saturating_sub__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.saturating_sub(b), u63::new(2).unwrap());
	}
	#[test]
	fn saturating_sub__at_min() {
		let a = u63::new(1).unwrap();
		let b = u63::new(1).unwrap();
		assert_eq!(a.saturating_sub(b), u63::MIN);
	}
	#[test]
	fn saturating_sub__underflow() {
		let a = u63::MIN;
		let b = u63::new(1).unwrap();
		assert_eq!(a.saturating_sub(b), u63::MIN);
	}
	
	//		trailing_ones														
	#[test]
	fn trailing_ones__all() {
		assert_eq!(u63::MAX.trailing_ones(), 63);
	}
	#[test]
	fn trailing_ones__none() {
		assert_eq!(u63::MIN.trailing_ones(), 0);
	}
	#[test]
	fn trailing_ones__some() {
		assert_eq!(u63::new(1).unwrap().trailing_ones(),      1);
		assert_eq!(u63::new(0b1010).unwrap().trailing_ones(), 0);
		assert_eq!((!(u63::MAX << 2)).trailing_ones(),        2);
	}
	
	//		trailing_zeros														
	#[test]
	fn trailing_zeros__all() {
		assert_eq!(u63::MIN.trailing_zeros(), 63);
	}
	#[test]
	fn trailing_zeros__none() {
		assert_eq!(u63::MAX.trailing_zeros(), 0);
	}
	#[test]
	fn trailing_zeros__some() {
		assert_eq!(u63::new(1).unwrap().trailing_zeros(),      0);
		assert_eq!(u63::new(0b1010).unwrap().trailing_zeros(), 1);
		assert_eq!((u63::MAX << 2).trailing_zeros(),           2);
	}
	
	//		wrapping_add														
	#[test]
	fn wrapping_add__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.wrapping_add(b), u63::new(8).unwrap());
	}
	#[test]
	fn wrapping_add__overflow_by_one() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.wrapping_add(b), u63::MIN);
	}
	#[test]
	fn wrapping_add__overflow_by_many() {
		let a = u63::new(i64::MAX as u64 - 1).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.wrapping_add(b), u63::new(1).unwrap());
	}
	
	//		wrapping_div														
	#[test]
	fn wrapping_div__normal() {
		let a = u63::new(6).unwrap();
		let b = u63::new(2).unwrap();
		assert_eq!(a.wrapping_div(b), u63::new(3).unwrap());
	}
	#[test]
	fn wrapping_div__by_zero() {
		let a = u63::new(6).unwrap();
		let b = u63::new(0).unwrap();
		assert_eq!(a.wrapping_div(b), u63::MAX);
	}
	
	//		wrapping_mul														
	#[test]
	fn wrapping_mul__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.wrapping_mul(b), u63::new(15).unwrap());
	}
	#[test]
	fn wrapping_mul__at_max() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		assert_eq!(a.wrapping_mul(b), u63::MAX);
	}
	#[test]
	fn wrapping_mul__overflow_small() {
		let a = u63::MAX;
		let b = u63::new(2).unwrap();
		assert_eq!(a.wrapping_mul(b), u63::MAX - u63::new(1).unwrap());
	}
	#[test]
	fn wrapping_mul__overflow_large() {
		let a = u63::MAX;
		let b = u63::MAX;
		assert_eq!(a.wrapping_mul(b), u63::new(1).unwrap());
	}
	
	//		wrapping_pow														
	#[test]
	fn wrapping_pow__normal() {
		assert_eq!(u63::new(2).unwrap().wrapping_pow(3), u63::new(8).unwrap());
	}
	#[test]
	fn wrapping_pow__at_max() {
		let max_power = 62;
		assert_eq!(u63::new(2).unwrap().wrapping_pow(max_power), u63::new(1_u64 << max_power).unwrap());
	}
	#[test]
	fn wrapping_pow__overflow() {
		assert_eq!(u63::new(2).unwrap().wrapping_pow(63), u63::MIN);
	}
	#[test]
	fn wrapping_pow__zero() {
		let base = u63::new(0).unwrap();
		assert_eq!(base.wrapping_pow(0), u63::new(1).unwrap());
		assert_eq!(base.wrapping_pow(1), u63::new(0).unwrap());
	}
	
	//		wrapping_rem														
	#[test]
	fn wrapping_rem__normal() {
		let a = u63::new(7).unwrap();
		let b = u63::new(4).unwrap();
		assert_eq!(a.wrapping_rem(b), u63::new(3).unwrap());
	}
	#[test]
	fn wrapping_rem__by_zero() {
		let a = u63::new(7).unwrap();
		let b = u63::new(0).unwrap();
		assert_eq!(a.wrapping_rem(b), u63::MAX);
	}
	
	//		wrapping_sub														
	#[test]
	fn wrapping_sub__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::new(2).unwrap());
	}
	#[test]
	fn wrapping_sub__at_min() {
		let a = u63::new(1).unwrap();
		let b = u63::new(1).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::MIN);
	}
	#[test]
	fn wrapping_sub__underflow_by_one() {
		let a = u63::MIN;
		let b = u63::new(1).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::MAX);
	}
	#[test]
	fn wrapping_sub__underflow_by_many() {
		let a = u63::new(1).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a.wrapping_sub(b), u63::MAX - u63::new(1).unwrap());
	}
}

mod derived_traits {
	use super::*;
	
	//		Debug																
	#[test]
	fn debug() {
		assert_eq!(format!("{:?}", u63::MIN),              "u63(0)");
		assert_eq!(format!("{:?}", u63::new(42).unwrap()), "u63(42)");
		assert_eq!(format!("{:?}", u63::MAX),              format!("u63({})", i64::MAX));
	}
	
	//		Default																
	#[test]
	fn default() {
		assert_eq!(u63::default(), u63::MIN);
	}
	
	//		Deserialize															
	#[test]
	fn deserialize() {
		assert_ok_eq!(serde_json::from_str::<u63>("42"), u63::new(42).unwrap());
	}
	
	//		Eq																	
	#[test]
	fn eq() {
		let a = u63::new(1).unwrap();
		let b = u63::new(2).unwrap();
		let c = u63::new(2).unwrap();
		
		assert_ne!(a, b);
		assert_eq!(b, c);
	}
	
	//		Hash																
	#[test]
	fn hash() {
		let mut set = HashSet::new();
		let a = u63::new(42).unwrap();
		let b = u63::new(42).unwrap();
		let c = u63::new(43).unwrap();
		
		_ = set.insert(a);
		assert!( set.contains(&b));
		assert!(!set.contains(&c));
	}
	
	//		Ord																	
	#[test]
	fn ord() {
		let a = u63::new(1).unwrap();
		let b = u63::new(2).unwrap();
		let c = u63::new(2).unwrap();
		
		assert!(a < b);
		assert!(b > a);
		assert!(b >= c);
		assert!(b <= c);
		assert_eq!(b.cmp(&c), Ordering::Equal);
	}
	
	//		Serialize															
	#[test]
	fn serialize() {
		assert_ok_eq!(serde_json::to_string(&u63::new(42).unwrap()), "42");
	}
}

mod traits {
	use super::*;
	
	//		Add																	
	#[test]
	fn add__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a + b, u63::new(8).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn add__overflow() {
		let a = u63::MAX;
		let b = u63::new(1).unwrap();
		let _ = a + b;
	}
	
	//		AddAssign															
	#[test]
	fn add_assign__normal() {
		let mut a = u63::new(5).unwrap();
		let     b = u63::new(3).unwrap();
		a += b;
		assert_eq!(a, u63::new(8).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn add_assign__overflow() {
		let mut a = u63::MAX;
		let     b = u63::new(1).unwrap();
		a += b;
	}
	
	//		Binary																
	#[test]
	fn binary() {
		assert_eq!(format!("{:b}",  u63::new(42).unwrap()), "101010");
		assert_eq!(format!("{:#b}", u63::new(42).unwrap()), "0b101010");
	}
	
	//		BitAnd																
	#[test]
	fn bitand__normal() {
		let a = u63::new(0b1100).unwrap();
		let b = u63::new(0b1010).unwrap();
		assert_eq!(a & b, u63::new(0b1000).unwrap());
	}
	#[test]
	fn bitand__all_bits_set() {
		assert_eq!(u63::MAX & u63::MAX, u63::MAX);
	}
	#[test]
	fn bitand__zero_with_max() {
		assert_eq!(u63::MIN & u63::MAX, u63::MIN);
	}
	#[test]
	fn bitand__highest_valid_bit() {
		let high_bit = u63::new(1_u64 << 62).unwrap();
		assert_eq!(high_bit & u63::MAX, high_bit);
	}
	
	//		BitAndAssign														
	#[test]
	fn bitand_assign__normal() {
		let mut a = u63::new(0b1100).unwrap();
		let     b = u63::new(0b1010).unwrap();
		a &= b;
		assert_eq!(a, u63::new(0b1000).unwrap());
	}
	#[test]
	fn bitand_assign__all_bits() {
		let mut a = u63::MAX;
		a &= u63::MAX;
		assert_eq!(a, u63::MAX);
	}
	#[test]
	fn bitand_assign__with_zero() {
		let mut a = u63::MAX;
		a &= u63::MIN;
		assert_eq!(a, u63::MIN);
	}
	
	//		BitOr																
	#[test]
	fn bitor__normal() {
		let a = u63::new(0b1100).unwrap();
		let b = u63::new(0b1010).unwrap();
		assert_eq!(a | b, u63::new(0b1110).unwrap());
	}
	#[test]
	fn bitor__with_zero() {
		let a = u63::new(0b1100).unwrap();
		assert_eq!(a | u63::MIN, a);
	}
	#[test]
	fn bitor__with_max() {
		let a = u63::new(0b1100).unwrap();
		assert_eq!(a | u63::MAX, u63::MAX);
	}
	
	//		BitOrAssign															
	#[test]
	fn bitor_assign__normal() {
		let mut a = u63::new(0b1100).unwrap();
		let     b = u63::new(0b1010).unwrap();
		a |= b;
		assert_eq!(a, u63::new(0b1110).unwrap());
	}
	#[test]
	fn bitor_assign__with_zero() {
		let mut a = u63::new(0b1100).unwrap();
		a |= u63::MIN;
		assert_eq!(a, u63::new(0b1100).unwrap());
	}
	#[test]
	fn bitor_assign__with_max() {
		let mut a = u63::new(0b1100).unwrap();
		a |= u63::MAX;
		assert_eq!(a, u63::MAX);
	}
	
	//		BitXor																
	#[test]
	fn bitxor__normal() {
		let a = u63::new(0b1100).unwrap();
		let b = u63::new(0b1010).unwrap();
		assert_eq!(a ^ b, u63::new(0b0110).unwrap());
	}
	#[test]
	fn bitxor__with_zero() {
		let a = u63::new(0b1100).unwrap();
		assert_eq!(a ^ u63::MIN, a);
	}
	#[test]
	fn bitxor__with_max() {
		let a = u63::new(0b1100).unwrap();
		assert_eq!(a ^ u63::MAX, !a & u63::MAX);
	}
	
	//		BitXorAssign														
	#[test]
	fn bitxor_assign__normal() {
		let mut a = u63::new(0b1100).unwrap();
		let     b = u63::new(0b1010).unwrap();
		a ^= b;
		assert_eq!(a, u63::new(0b0110).unwrap());
	}
	#[test]
	fn bitxor_assign__with_zero() {
		let mut a = u63::new(0b1100).unwrap();
		a ^= u63::MIN;
		assert_eq!(a, u63::new(0b1100).unwrap());
	}
	#[test]
	fn bitxor_assign__with_max() {
		let mut a = u63::new(0b1100).unwrap();
		a ^= u63::MAX;
		assert_eq!(a, !u63::new(0b1100).unwrap() & u63::MAX);
	}
	
	//		Deref																
	#[test]
	fn deref() {
		let value = u63::new(42).unwrap();
		assert_eq!(*value, 42_u64);
	}
	
	//		Display																
	#[test]
	fn display() {
		let value = u63::new(42).unwrap();
		assert_eq!(format!("{value}"), "42");
		assert_eq!(value.to_string(),  "42");
	}
	
	//		Div																	
	#[test]
	fn div__normal() {
		let a = u63::new(6).unwrap();
		let b = u63::new(2).unwrap();
		assert_eq!(a / b, u63::new(3).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to divide by zero")]
	fn div__by_zero() {
		let a = u63::new(6).unwrap();
		let b = u63::new(0).unwrap();
		let _ = a / b;
	}
	
	//		DivAssign															
	#[test]
	fn div_assign__normal() {
		let mut a = u63::new(6).unwrap();
		let     b = u63::new(2).unwrap();
		a /= b;
		assert_eq!(a, u63::new(3).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to divide by zero")]
	fn div_assign__by_zero() {
		let mut a = u63::new(6).unwrap();
		let     b = u63::new(0).unwrap();
		a /= b;
	}
	
	//		LowerHex															
	#[test]
	fn lowerhex() {
		assert_eq!(format!("{:x}",  u63::new(42).unwrap()), "2a");
		assert_eq!(format!("{:#x}", u63::new(42).unwrap()), "0x2a");
	}
	
	//		LowerExp															
	#[test]
	fn lowerexp() {
		assert_eq!(format!("{:e}", u63::new(42).unwrap()), "4.2e1");
		assert_eq!(format!("{:e}", u63::MIN),              "0e0");
		assert_eq!(format!("{:e}", u63::MAX),              format!("{:e}", i64::MAX));
	}
	
	//		Mul																	
	#[test]
	fn mul__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a * b, u63::new(15).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn mul__overflow() {
		let a = u63::MAX;
		let b = u63::new(2).unwrap();
		let _ = a * b;
	}
	
	//		MulAssign															
	#[test]
	fn mul_assign__normal() {
		let mut a = u63::new(6).unwrap();
		let     b = u63::new(2).unwrap();
		a *= b;
		assert_eq!(a, u63::new(12).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn mul_assign__overflow() {
		let mut a = u63::MAX;
		let     b = u63::new(2).unwrap();
		a *= b;
	}
	
	//		Not																	
	#[test]
	fn not__zero() {
		assert_eq!(!u63::MIN, u63::MAX);
	}
	#[test]
	fn not__max() {
		assert_eq!(!u63::MAX, u63::MIN);
	}
	#[test]
	fn not__pattern() {
		assert_eq!(
			!u63::new(0b1010).unwrap(),
			u63::new(0b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_0101).unwrap()
		);
	}
	
	//		Octal																
	#[test]
	fn octal() {
		assert_eq!(format!("{:o}",  u63::new(42).unwrap()), "52");
		assert_eq!(format!("{:#o}", u63::new(42).unwrap()), "0o52");
		assert_eq!(format!("{:o}",  u63::MIN),              "0");
		assert_eq!(format!("{:o}",  u63::MAX),              format!("{:o}", i64::MAX));
	}
	
	//		Product																
	#[test]
	fn product__empty() {
		let values: Vec<u63> = vec![];
		assert_eq!(values.into_iter().product::<u63>(), u63::new(1).unwrap());
	}
	#[test]
	fn product__single() {
		let values = vec![
			u63::new(42).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::new(42).unwrap());
	}
	#[test]
	fn product__multiple_non_zero() {
		let values = vec![
			u63::new(2).unwrap(),
			u63::new(3).unwrap(),
			u63::new(4).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::new(24).unwrap());
	}
	#[test]
	fn product__multiple_with_zero() {
		let values = vec![
			u63::new(2).unwrap(),
			u63::new(0).unwrap(),
			u63::new(4).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::new(0).unwrap());
	}
	#[test]
	fn product__at_max() {
		let values = vec![
			u63::MAX,
			u63::new(1).unwrap(),
		];
		assert_eq!(values.into_iter().product::<u63>(), u63::MAX);
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn product__overflow() {
		let values = vec![
			u63::MAX,
			u63::new(2).unwrap(),
		];
		let _ = values.into_iter().product::<u63>();
	}
	
	//		Product<&>															
	#[test]
	fn product_ref__empty() {
		let values = [];
		assert_eq!(values.iter().product::<u63>(), u63::new(1).unwrap());
	}
	#[test]
	fn product_ref__single() {
		let values = [
			u63::new(42).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::new(42).unwrap());
	}
	#[test]
	fn product_ref__multiple_non_zero() {
		let values = [
			u63::new(2).unwrap(),
			u63::new(3).unwrap(),
			u63::new(4).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::new(24).unwrap());
	}
	#[test]
	fn product_ref__multiple_with_zero() {
		let values = [
			u63::new(2).unwrap(),
			u63::new(0).unwrap(),
			u63::new(4).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::new(0).unwrap());
	}
	#[test]
	fn product_ref__at_max() {
		let values = [
			u63::MAX,
			u63::new(1).unwrap(),
		];
		assert_eq!(values.iter().product::<u63>(), u63::MAX);
	}
	#[test]
	#[should_panic(expected = "Attempt to multiply overflowed")]
	fn product_ref__overflow() {
		let values = [
			u63::MAX,
			u63::new(2).unwrap(),
		];
		let _ = values.iter().product::<u63>();
	}
	
	//		Rem																	
	#[test]
	fn rem__normal() {
		let a = u63::new(7).unwrap();
		let b = u63::new(4).unwrap();
		assert_eq!(a % b, u63::new(3).unwrap());
	}
	#[test]
	fn rem__zero() {
		let a = u63::new(8).unwrap();
		let b = u63::new(4).unwrap();
		assert_eq!(a % b, u63::new(0).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to calculate remainder with a divisor of zero")]
	fn rem__by_zero() {
		let a = u63::new(7).unwrap();
		let b = u63::new(0).unwrap();
		let _ = a % b;
	}
	
	//		RemAssign															
	#[test]
	fn rem_assign__normal() {
		let mut a = u63::new(7).unwrap();
		let     b = u63::new(4).unwrap();
		a %= b;
		assert_eq!(a, u63::new(3).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to calculate remainder with a divisor of zero")]
	fn rem_assign__by_zero() {
		let mut a = u63::new(7).unwrap();
		let     b = u63::new(0).unwrap();
		a %= b;
	}
	
	//		Shl																	
	#[test]
	fn shl__normal() {
		assert_eq!(u63::new(0b1  ).unwrap() << 3, u63::new(0b1000 ).unwrap());
		assert_eq!(u63::new(0b101).unwrap() << 2, u63::new(0b10100).unwrap());
	}
	
	#[test]
	fn shl__zero_shift() {
		let value = u63::new(42).unwrap();
		assert_eq!(value << 0, value);
	}
	
	#[test]
	fn shl__overflow() {
		assert_eq!(u63::new(1).unwrap() << 63, u63::MIN);
		assert_eq!(u63::MAX             << 1,  u63::MAX >> 1 << 1);
	}
	
	#[test]
	fn shl__large_shift() {
		assert_eq!(u63::new(1).unwrap() << 65, u63::new(2).unwrap());
	}
	
	//		ShlAssign															
	#[test]
	fn shl_assign() {
		let mut value = u63::new(0b1).unwrap();
		value <<= 3;
		assert_eq!(value, u63::new(0b1000).unwrap());
	}
	
	//		Shr																	
	#[test]
	fn shr__normal() {
		assert_eq!(u63::new(0b1000 ).unwrap() >> 3, u63::new(0b1  ).unwrap());
		assert_eq!(u63::new(0b10100).unwrap() >> 2, u63::new(0b101).unwrap());
	}
	
	#[test]
	fn shr__zero_shift() {
		let value = u63::new(42).unwrap();
		assert_eq!(value >> 0, value);
	}
	
	#[test]
	fn shr__underflow() {
		assert_eq!(u63::new(1).unwrap() >> 63, u63::MIN);
		assert_eq!(u63::MAX             >> 62, u63::new(1).unwrap());
		assert_eq!(u63::MAX             >> 63, u63::MIN);
	}
	
	#[test]
	fn shr__large_shift() {
		assert_eq!(u63::new(0b1000).unwrap() >> 65, u63::new(0b0100).unwrap());
	}
	
	//		ShrAssign															
	#[test]
	fn shr_assign() {
		let mut value = u63::new(0b1000).unwrap();
		value >>= 3;
		assert_eq!(value, u63::new(0b1).unwrap());
	}
	
	//		Sub																	
	#[test]
	fn sub__normal() {
		let a = u63::new(5).unwrap();
		let b = u63::new(3).unwrap();
		assert_eq!(a - b, u63::new(2).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to subtract overflowed")]
	fn sub__underflow() {
		let a = u63::MIN;
		let b = u63::new(1).unwrap();
		let _ = a - b;
	}
	
	//		SubAssign															
	#[test]
	fn sub_assign__normal() {
		let mut a = u63::new(5).unwrap();
		let     b = u63::new(3).unwrap();
		a -= b;
		assert_eq!(a, u63::new(2).unwrap());
	}
	#[test]
	#[should_panic(expected = "Attempt to subtract overflowed")]
	fn sub_assign__underflow() {
		let mut a = u63::MIN;
		let     b = u63::new(1).unwrap();
		a -= b;
	}
	
	//		Sum																	
	#[test]
	fn sum__empty() {
		let values: Vec<u63> = vec![];
		assert_eq!(values.into_iter().sum::<u63>(), u63::new(0).unwrap());
	}
	#[test]
	fn sum__single() {
		let values = vec![
			u63::new(42).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::new(42).unwrap());
	}
	#[test]
	fn sum__multiple_non_zero() {
		let values = vec![
			u63::new(1).unwrap(),
			u63::new(2).unwrap(),
			u63::new(3).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::new(6).unwrap());
	}
	#[test]
	fn sum__multiple_with_zero() {
		let values = vec![
			u63::new(1).unwrap(),
			u63::new(0).unwrap(),
			u63::new(3).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::new(4).unwrap());
	}
	#[test]
	fn sum__at_max() {
		let values = vec![
			u63::MAX - u63::new(1).unwrap(),
			u63::new(1).unwrap(),
		];
		assert_eq!(values.into_iter().sum::<u63>(), u63::MAX);
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn sum__overflow() {
		let values = vec![
			u63::MAX,
			u63::new(1).unwrap(),
		];
		let _ = values.into_iter().sum::<u63>();
	}
	
	//		Sum<&>																
	#[test]
	fn sum_ref__empty() {
		let values = [];
		assert_eq!(values.iter().sum::<u63>(), u63::new(0).unwrap());
	}
	#[test]
	fn sum_ref__single() {
		let values = [
			u63::new(42).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::new(42).unwrap());
	}
	#[test]
	fn sum_ref__multiple_non_zero() {
		let values = [
			u63::new(1).unwrap(),
			u63::new(2).unwrap(),
			u63::new(3).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::new(6).unwrap());
	}
	#[test]
	fn sum_ref__multiple_with_zero() {
		let values = [
			u63::new(1).unwrap(),
			u63::new(0).unwrap(),
			u63::new(3).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::new(4).unwrap());
	}
	#[test]
	fn sum_ref__at_max() {
		let values = [
			u63::MAX - u63::new(1).unwrap(),
			u63::new(1).unwrap(),
		];
		assert_eq!(values.iter().sum::<u63>(), u63::MAX);
	}
	#[test]
	#[should_panic(expected = "Attempt to add overflowed")]
	fn sum_ref__overflow() {
		let values = [
			u63::MAX,
			u63::new(1).unwrap(),
		];
		let _ = values.iter().sum::<u63>();
	}
	
	//		UpperExp															
	#[test]
	fn upperexp() {
		assert_eq!(format!("{:E}", u63::new(42).unwrap()), "4.2E1");
		assert_eq!(format!("{:E}", u63::MIN),              "0E0");
		assert_eq!(format!("{:E}", u63::MAX),              format!("{:E}", i64::MAX));
	}
	
	//		UpperHex															
	#[test]
	fn upperhex() {
		assert_eq!(format!("{:X}",  u63::new(42).unwrap()), "2A");
		assert_eq!(format!("{:#X}", u63::new(42).unwrap()), "0x2A");
	}
}

mod conversions {
	use super::*;
	
	//		From: u8 -> u63														
	#[test]
	fn from__u8() {
		assert_eq!(u63::from(42_u8), u63::new(42).unwrap());
	}
	
	//		From: u16 -> u63													
	#[test]
	fn from__u16() {
		assert_eq!(u63::from(0_u16),    u63::MIN);
		assert_eq!(u63::from(42_u16),   u63::new(42).unwrap());
		assert_eq!(u63::from(u16::MAX), u63::new(u16::MAX as u64).unwrap());
	}
	
	//		From: u32 -> u63													
	#[test]
	fn from__u32() {
		assert_eq!(u63::from(0_u32),    u63::MIN);
		assert_eq!(u63::from(42_u32),   u63::new(42).unwrap());
		assert_eq!(u63::from(u32::MAX), u63::new(u32::MAX as u64).unwrap());
	}
	
	//		From: u63 -> i64													
	#[test]
	fn from__to_i64() {
		assert_eq!(i64::from(u63::MIN),              0_i64);
		assert_eq!(i64::from(u63::new(42).unwrap()), 42_i64);
		assert_eq!(i64::from(u63::MAX),              i64::MAX);
	}
	
	//		From: u63 -> i128													
	#[test]
	fn from__to_i128() {
		assert_eq!(i128::from(u63::MIN),              0_i128);
		assert_eq!(i128::from(u63::new(42).unwrap()), 42_i128);
		assert_eq!(i128::from(u63::MAX),              i64::MAX as i128);
	}
	
	//		From: u63 -> u64													
	#[test]
	fn from__to_u64() {
		assert_eq!(u64::from(u63::MIN),              0_u64);
		assert_eq!(u64::from(u63::new(42).unwrap()), 42_u64);
		assert_eq!(u64::from(u63::MAX),              i64::MAX as u64);
	}
	
	//		From: u63 -> u128													
	#[test]
	fn from__to_u128() {
		assert_eq!(u128::from(u63::MIN),              0_u128);
		assert_eq!(u128::from(u63::new(42).unwrap()), 42_u128);
		assert_eq!(u128::from(u63::MAX),              i64::MAX as u128);
	}
	
	//		FromSql																
	#[test]
	fn from_sql__i32() {
		assert_ok_eq!(u63::from_sql(&Type::INT4, &42_i32.to_be_bytes()), u63::new(42).unwrap());
	}
	#[test]
	fn from_sql__i64() {
		assert_ok_eq!(u63::from_sql(&Type::INT8, &42_i64.to_be_bytes()), u63::new(42).unwrap());
	}
	#[test]
	fn from_sql__invalid_type() {
		let err = u63::from_sql(&Type::TEXT, &[0_u8; 8]);
		assert_err!(&err);
		assert_eq!(err.unwrap_err().to_string(), "Invalid type for u63: text");
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
		assert!(!<u63 as FromSql>::accepts(&Type::TEXT));
		assert!(!<u63 as FromSql>::accepts(&Type::FLOAT4));
	}
	
	//		FromStr																
	#[test]
	fn from_str__valid() {
		assert_ok_eq!( "0".parse::<u63>(),                 u63::MIN);
		assert_ok_eq!("42".parse::<u63>(),                 u63::new(42).unwrap());
		assert_ok_eq!(i64::MAX.to_string().parse::<u63>(), u63::MAX);
	}
	#[test]
	fn from_str__invalid_format() {
		assert_err_eq!("abc".parse::<u63>(),   ConversionError::ParseIntError(u64::from_str("abc").unwrap_err()));
		assert_err_eq!("12.34".parse::<u63>(), ConversionError::ParseIntError(u64::from_str("12.34").unwrap_err()));
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
		match u63::new(42).unwrap().to_sql(&Type::INT8, &mut bytes).unwrap() {
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
		assert!(!<u63 as FromSql>::accepts(&Type::TEXT));
		assert!(!<u63 as FromSql>::accepts(&Type::FLOAT4));
	}
	
	//		TryFrom: i8 -> u63													
	#[test]
	fn try_from__i8__valid() {
		assert_ok_eq!(u63::try_from( 0_i8),   u63::MIN);
		assert_ok_eq!(u63::try_from(42_i8),   u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(i8::MAX), u63::new(i8::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i8__negative() {
		assert_err_eq!(u63::try_from(-1_i8),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i8::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i16 -> u63													
	#[test]
	fn try_from__i16__valid() {
		assert_ok_eq!(u63::try_from( 0_i16),   u63::MIN);
		assert_ok_eq!(u63::try_from(42_i16),   u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(i16::MAX), u63::new(i16::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i16__negative() {
		assert_err_eq!(u63::try_from(-1_i16),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i16::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i32 -> u63													
	#[test]
	fn try_from__i32__valid() {
		assert_ok_eq!(u63::try_from( 0_i32),   u63::MIN);
		assert_ok_eq!(u63::try_from(42_i32),   u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(i32::MAX), u63::new(i32::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i32__negative() {
		assert_err_eq!(u63::try_from(-1_i32),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i32::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i64 -> u63													
	#[test]
	fn try_from__i64__valid() {
		assert_ok_eq!(u63::try_from( 0_i64),   u63::MIN);
		assert_ok_eq!(u63::try_from(42_i64),   u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(i32::MAX), u63::new(i32::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__i64__negative() {
		assert_err_eq!(u63::try_from(-1_i64),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(i64::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: i128 -> u63												
	#[test]
	fn try_from__i128__valid() {
		assert_ok_eq!(u63::try_from( 0_i128),          u63::MIN);
		assert_ok_eq!(u63::try_from(42_i128),          u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(i64::MAX as i128), u63::MAX);
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
		assert_ok_eq!(u63::try_from( 0_isize),   u63::MIN);
		assert_ok_eq!(u63::try_from(42_isize),   u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(isize::MAX), u63::new(isize::MAX as u64).unwrap());
	}
	#[test]
	fn try_from__isize__negative() {
		assert_err_eq!(u63::try_from(-1_isize),   ConversionError::ValueIsNegative);
		assert_err_eq!(u63::try_from(isize::MIN), ConversionError::ValueIsNegative);
	}
	
	//		TryFrom: u63 -> i8													
	#[test]
	fn try_from__to_i8__valid() {
		assert_ok_eq!(i8::try_from(u63::MIN),                          0_i8);
		assert_ok_eq!(i8::try_from(u63::new(42).unwrap()),             42_i8);
		assert_ok_eq!(i8::try_from(u63::new(i8::MAX as u64).unwrap()), i8::MAX);
	}
	#[test]
	fn try_from__to_i8__too_large() {
		assert_err_eq!(i8::try_from(u63::new(i8::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> i16													
	#[test]
	fn try_from__to_i16__valid() {
		assert_ok_eq!(i16::try_from(u63::MIN),                           0_i16);
		assert_ok_eq!(i16::try_from(u63::new(42).unwrap()),              42_i16);
		assert_ok_eq!(i16::try_from(u63::new(i16::MAX as u64).unwrap()), i16::MAX);
	}
	#[test]
	fn try_from__to_i16__too_large() {
		assert_err_eq!(i16::try_from(u63::new(i16::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> i32													
	#[test]
	fn try_from__to_i32__valid() {
		assert_ok_eq!(i32::try_from(u63::MIN),                           0_i32);
		assert_ok_eq!(i32::try_from(u63::new(42).unwrap()),              42_i32);
		assert_ok_eq!(i32::try_from(u63::new(i32::MAX as u64).unwrap()), i32::MAX);
	}
	#[test]
	fn try_from__to_i32__too_large() {
		assert_err_eq!(i32::try_from(u63::new(i32::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> isize												
	#[test]
	fn try_from__to_isize__valid() {
		assert_ok_eq!(isize::try_from(u63::MIN),                             0_isize);
		assert_ok_eq!(isize::try_from(u63::new(42).unwrap()),                42_isize);
		assert_ok_eq!(isize::try_from(u63::new(isize::MAX as u64).unwrap()), isize::MAX);
	}
	#[test]
	fn try_from__to_isize__too_large() {
		//	Only test on 32-bit platforms where isize::MAX < u63::MAX
		if (isize::MAX as u64) < u63::MAX.as_u64() {
			assert_err_eq!(
				isize::try_from(u63::new(isize::MAX as u64 + 1).unwrap()),
				ConversionError::ValueTooLarge
			);
		}
	}
	
	//		TryFrom: u63 -> u8													
	#[test]
	fn try_from__to_u8__valid() {
		assert_ok_eq!(u8::try_from(u63::MIN),                          0_u8);
		assert_ok_eq!(u8::try_from(u63::new(42).unwrap()),             42_u8);
		assert_ok_eq!(u8::try_from(u63::new(u8::MAX as u64).unwrap()), u8::MAX);
	}
	#[test]
	fn try_from__to_u8__too_large() {
		assert_err_eq!(u8::try_from(u63::new(u8::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> u16													
	#[test]
	fn try_from__to_u16__valid() {
		assert_ok_eq!(u16::try_from(u63::MIN),                           0_u16);
		assert_ok_eq!(u16::try_from(u63::new(42).unwrap()),              42_u16);
		assert_ok_eq!(u16::try_from(u63::new(u16::MAX as u64).unwrap()), u16::MAX);
	}
	#[test]
	fn try_from__to_u16__too_large() {
		assert_err_eq!(u16::try_from(u63::new(u16::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> u32													
	#[test]
	fn try_from__to_u32__valid() {
		assert_ok_eq!(u32::try_from(u63::MIN),                           0_u32);
		assert_ok_eq!(u32::try_from(u63::new(42).unwrap()),              42_u32);
		assert_ok_eq!(u32::try_from(u63::new(u32::MAX as u64).unwrap()), u32::MAX);
	}
	#[test]
	fn try_from__to_u32__too_large() {
		assert_err_eq!(u32::try_from(u63::new(u32::MAX as u64 + 1).unwrap()), ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u63 -> usize												
	#[test]
	fn try_from__to_usize__valid() {
		assert_ok_eq!(usize::try_from(u63::MIN),              0_usize);
		assert_ok_eq!(usize::try_from(u63::new(42).unwrap()), 42_usize);
	}
	#[test]
	fn try_from__to_usize__too_large() {
		//	Only test on 32-bit platforms where usize::MAX < u63::MAX
		if (usize::MAX as u64) < u63::MAX.as_u64() {
			//	Use a value definitely larger than usize::MAX but within u63 range
			let large_value = u63::new(usize::MAX as u64).unwrap() + u63::new(1).unwrap();
			assert_err_eq!(
				usize::try_from(large_value),
				ConversionError::ValueTooLarge
			);
		}
	}
	
	//		TryFrom: u64 -> u63													
	#[test]
	fn try_from__u64__valid() {
		assert_ok_eq!(u63::try_from( 0_u64),          u63::MIN);
		assert_ok_eq!(u63::try_from(42_u64),          u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(i64::MAX as u64), u63::MAX);
	}
	#[test]
	fn try_from__u64__too_large() {
		assert_err_eq!(u63::try_from(i64::MAX as u64 + 1), ConversionError::ValueTooLarge);
		assert_err_eq!(u63::try_from(u64::MAX),            ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: u128 -> u63												
	#[test]
	fn try_from__u128__valid() {
		assert_ok_eq!(u63::try_from( 0_u128),          u63::MIN);
		assert_ok_eq!(u63::try_from(42_u128),          u63::new(42).unwrap());
		assert_ok_eq!(u63::try_from(i64::MAX as u128), u63::MAX);
	}
	#[test]
	fn try_from__u128__too_large() {
		assert_err_eq!(u63::try_from(i64::MAX as u128 + 1), ConversionError::ValueTooLarge);
		assert_err_eq!(u63::try_from(u128::MAX),            ConversionError::ValueTooLarge);
	}
	
	//		TryFrom: usize -> u63												
	#[test]
	fn try_from__usize__valid() {
		assert_ok_eq!(u63::try_from( 0_usize), u63::MIN);
		assert_ok_eq!(u63::try_from(42_usize), u63::new(42).unwrap());
		//	Can't test MAX as it varies by platform
	}
	#[test]
	fn try_from__usize__too_large() {
		//	Only test if usize::MAX > u63::MAX (64-bit platforms)
		if usize::MAX as u64 > u63::MAX.as_u64() {
			assert_err_eq!(
				u63::try_from(usize::try_from(u63::MAX.as_u64()).unwrap() + 1),
				ConversionError::ValueTooLarge
			);
		}
	}
}


