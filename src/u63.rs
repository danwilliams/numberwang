//! Custom u63 type.



//		Packages

use crate::errors::ConversionError;
use bytes::BytesMut;
use core::{
	fmt::{Display, Formatter, self},
	ops::{Add, Deref, Div, Mul, Rem, Sub},
};
use serde::{Deserialize, Serialize};
use std::{
	error::Error,
	io::{Error as IoError, ErrorKind as IoErrorKind},
};
use tokio_postgres::types::{FromSql, IsNull, ToSql, Type, to_sql_checked};



//		Structs

//		u63																		
/// A 63-bit unsigned integer.
/// 
/// This type is used to represent the crossover between a [`u64`] (which would
/// be the choice for the types used in Rust) and an [`i64`] (which is a
/// limitation of certain databases, e.g. PostgreSQL). This is necessary in
/// order to safely represent the values in the database without losing any
/// information.
/// 
/// It would also be possible to use a [`u64`] and convert to an [`i64`] but
/// use the sign bit as the most-significant bit, but this is not necessary at
/// present as the extra range is not needed, plus it would make the database
/// data less human-readable for those high values. There is also the potential
/// for conversion error elsewhere in the chain if taking that approach.
/// 
/// Therefore this type is used because we want an unsigned integer with the
/// maximum range possible.
/// 
/// # Arithmetic
/// 
/// This type implements the standard arithmetic operations, but with the
/// following caveats:
/// 
///   1. Addition, subtraction, and multiplication are saturating; i.e. they
///      will not overflow or underflow, but will truncate the result to fit
///      within the 63-bit range. If this is not desired behaviour then these
///      operations should be performed in a different manner.
///   2. Division by zero will not panic, but will instead return the maximum
///      possible value. Modulo by zero acts in the same way.
/// 
/// # Conversion
/// 
/// This type can be converted to and from any of the following types:
/// 
///   - [`u8`], [`u16`], [`u32`], [`u64`], [`u128`]
///   - [`i8`], [`i16`], [`i32`], [`i64`], [`i128`]
/// 
/// Where the conversion is lossless, [`From`] is implemented, and where it is
/// potentially lossy, [`TryFrom`] is implemented.
/// 
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[cfg_attr(    feature = "reasons",  allow(non_camel_case_types, reason = "Needed to fit with convention"))]
#[cfg_attr(not(feature = "reasons"), allow(non_camel_case_types))]
pub struct u63(u64);

//󰭅		u63																		
impl u63 {
	/// The maximum value for a `u63`.
	pub const MAX: Self = Self(i64::MAX as u64);
	
	//		as_u64																
	/// Represents the internal value as an unsigned 64-bit integer.
	#[must_use]
	pub const fn as_u64(&self) -> u64 {
		self.0
	}
	
	//		as_i64																
	/// Represents the internal value as a signed 64-bit integer.
	#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_wrap, reason = "Safe, as fully managed"))]
	#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_wrap))]
	#[must_use]
	pub const fn as_i64(&self) -> i64 {
		self.0 as i64
	}
}

//󰭅		Add																		
impl Add for u63 {
	type Output = Self;
	
	//		add																	
	fn add(self, rhs: Self) -> Self::Output {
		Self(self.0.saturating_add(rhs.0))
	}
}

//󰭅		Deref																	
impl Deref for u63 {
	type Target = u64;
	
	//		deref																
	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

//󰭅		Display																	
impl Display for u63 {
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}

//󰭅		Div																		
impl Div for u63 {
	type Output = Self;
	
	//		div																	
	fn div(self, rhs: Self) -> Self::Output {
		if rhs.0 == 0 {
			Self::MAX
		} else {
			#[cfg_attr(    feature = "reasons",  allow(clippy::arithmetic_side_effects, reason = "Already checked"))]
			#[cfg_attr(not(feature = "reasons"), allow(clippy::arithmetic_side_effects))]
			#[cfg_attr(    feature = "reasons",  allow(clippy::integer_division, reason = "Okay here, as intentional"))]
			#[cfg_attr(not(feature = "reasons"), allow(clippy::integer_division))]
			Self(self.0 / rhs.0)
		}
	}
}

//󰭅		From: u8 -> u63															
impl From<u8> for u63 {
	//		from																
	fn from(v: u8) -> Self {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		Self(v as u64)
	}
}

//󰭅		From: u16 -> u63														
impl From<u16> for u63 {
	//		from																
	fn from(v: u16) -> Self {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		Self(v as u64)
	}
}

//󰭅		From: u32 -> u63														
impl From<u32> for u63 {
	//		from																
	fn from(v: u32) -> Self {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		Self(v as u64)
	}
}

//󰭅		From: u63 -> i64														
impl From<u63> for i64 {
	//		from																
	#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_wrap, reason = "Safe, as fully managed"))]
	#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_wrap))]
	fn from(v: u63) -> Self {
		v.0 as Self
	}
}

//󰭅		From: u63 -> i128														
impl From<u63> for i128 {
	//		from																
	fn from(v: u63) -> Self {
		Self::from(v.0)
	}
}

//󰭅		From: u63 -> u64														
impl From<u63> for u64 {
	//		from																
	fn from(v: u63) -> Self {
		v.0
	}
}

//󰭅		From: u63 -> u128														
impl From<u63> for u128 {
	//		from																
	fn from(v: u63) -> Self {
		Self::from(v.0)
	}
}

//󰭅		FromSql																	
impl<'a> FromSql<'a> for u63 {
	//		from_sql															
	fn from_sql(ty: &Type, raw: &'a [u8]) -> Result<Self, Box<dyn Error + Sync + Send>> {
		match ty {
			&Type::INT4 => Self::try_from(i32::from_sql(ty, raw)?).map_err(Into::into),
			&Type::INT8 => Self::try_from(i64::from_sql(ty, raw)?).map_err(Into::into),
			unknown     => Err(Box::new(IoError::new(
				IoErrorKind::InvalidData,
				format!("Invalid type for u63: {unknown}"),
			))),
		}
	}
	
	//		accepts																
	fn accepts(ty: &Type) -> bool {
		matches!(*ty, Type::INT4 | Type::INT8)
	}
}

//󰭅		Mul																		
impl Mul for u63 {
	type Output = Self;
	
	//		mul																	
	fn mul(self, rhs: Self) -> Self::Output {
		Self(self.as_u64().saturating_mul(rhs.as_u64()).min(Self::MAX.as_u64()))
	}
}

//󰭅		Rem																		
impl Rem for u63 {
	type Output = Self;
	
	//		rem																	
	fn rem(self, rhs: Self) -> Self::Output {
		if rhs.0 == 0 {
			Self::MAX
		} else {
			#[cfg_attr(    feature = "reasons",  allow(clippy::arithmetic_side_effects, reason = "Already checked"))]
			#[cfg_attr(not(feature = "reasons"), allow(clippy::arithmetic_side_effects))]
			Self(self.0 % rhs.0)
		}
	}
}

//󰭅		Sub																		
impl Sub for u63 {
	type Output = Self;
	
	//		sub																	
	fn sub(self, rhs: Self) -> Self::Output {
		Self(self.0.saturating_sub(rhs.0))
	}
}

//󰭅		ToSql																	
impl ToSql for u63 {
	//		to_sql																
	fn to_sql(&self, ty: &Type, out: &mut BytesMut) -> Result<IsNull, Box<dyn Error + Sync + Send>> {
		i64::from(*self).to_sql(ty, out)
	}
	
	//		accepts																
	fn accepts(ty: &Type) -> bool {
		matches!(*ty, Type::INT4 | Type::INT8)
	}
	
	to_sql_checked!();
}

//󰭅		TryFrom: i8 -> u63														
impl TryFrom<i8> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i8) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: i16 -> u63														
impl TryFrom<i16> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i16) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: i32 -> u63														
impl TryFrom<i32> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i32) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: i64 -> u63														
impl TryFrom<i64> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i64) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_sign_loss, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_sign_loss))]
		(v >= 0).then_some(Self(v as u64)).ok_or(ConversionError::ValueIsNegative)
	}
}

//󰭅		TryFrom: i128 -> u63													
impl TryFrom<i128> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i128) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		if v < 0 {
			Err(ConversionError::ValueIsNegative)
		} else if v > i64::MAX as i128 {
			Err(ConversionError::ValueTooLarge)
		} else {
			#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
			#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
			#[cfg_attr(    feature = "reasons",  allow(clippy::cast_sign_loss, reason = "Already checked"))]
			#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_sign_loss))]
			Ok(Self(v as u64))
		}
	}
}

//󰭅		TryFrom: u63 -> i8														
impl TryFrom<u63> for i8 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> i16														
impl TryFrom<u63> for i16 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> i32														
impl TryFrom<u63> for i32 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> u8														
impl TryFrom<u63> for u8 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> u16														
impl TryFrom<u63> for u16 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> u32														
impl TryFrom<u63> for u32 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_lossless, reason = "Fine here"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_lossless))]
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u64 -> u63														
impl TryFrom<u64> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u64) -> Result<Self, Self::Error> {
		i64::try_from(v).is_ok().then_some(Self(v)).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u128 -> u63													
impl TryFrom<u128> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u128) -> Result<Self, Self::Error> {
		#[cfg_attr(    feature = "reasons",  allow(clippy::cast_possible_truncation, reason = "Already checked"))]
		#[cfg_attr(not(feature = "reasons"), allow(clippy::cast_possible_truncation))]
		(v <= i64::MAX as u128).then_some(Self(v as u64)).ok_or(ConversionError::ValueTooLarge)
	}
}


