//! Custom u63 type.



//		Modules

#[cfg(test)]
#[path = "tests/u63.rs"]
mod tests;



//		Packages

use crate::errors::ConversionError;
use bytes::BytesMut;
use core::{
	error::Error,
	fmt::{Binary, Display, Formatter, LowerExp, LowerHex, Octal, UpperExp, UpperHex, self},
	iter::{Product, Sum},
	ops::{Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign},
	ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr, ShrAssign},
	str::FromStr,
};
use serde::{Deserialize, Serialize};
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
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
/// This type implements the standard arithmetic operations following standard
/// Rust integer behavior:
/// 
///   1. In debug builds, arithmetic operations will panic on overflow.
///   2. In release builds, arithmetic operations will wrap.
///   3. Explicit saturating, wrapping, and checked arithmetic is available
///      through the respective methods.
/// 
/// Division by zero will panic, as with standard integer types.
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
#[expect(non_camel_case_types, reason = "Needed to fit with convention")]
pub struct u63(u64);

//󰭅		u63																		
impl u63 {
	/// The maximum value for a [`u63`].
	pub const BITS: u32 = 63_u32;
	
	/// The maximum value for a [`u63`].
	pub const MAX:  Self = Self(i64::MAX as u64);
	
	/// The minimum value for a [`u63`].
	pub const MIN:  Self = Self(0_u64);
	
	/// Mask the leading bit that is not part of the [`u63`].
	const MASK_LEADING:  u64 = 1 << 63;
	
	/// Mask the trailing bit that is not part of the [`u63`].
	const MASK_TRAILING: u64 = 1;
	
	//		new																	
	/// Creates a new [`u63`] from the given value.
	/// 
	/// # Parameters
	/// 
	/// * `value` - The value to create the [`u63`] from.
	/// 
	/// # Errors
	/// 
	/// Returns an error if the value is too large to fit in a [`u63`].
	/// 
	pub const fn new(value: u64) -> Result<Self, ConversionError> {
		if value > Self::MAX.0 {
			return Err(ConversionError::ValueTooLarge);
		}
		Ok(Self(value))
	}
	
	//		as_u64																
	/// Represents the internal value as an unsigned 64-bit integer.
	#[must_use]
	pub const fn as_u64(&self) -> u64 {
		self.0
	}
	
	//		as_i64																
	/// Represents the internal value as a signed 64-bit integer.
	#[expect(clippy::cast_possible_wrap, reason = "Safe, as fully managed")]
	#[must_use]
	pub const fn as_i64(&self) -> i64 {
		self.0 as i64
	}
	
	//		checked_add															
	/// Checked addition.
	/// 
	/// Computes `self + rhs`, returning [`None`] if overflow occurred.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to add to `self`.
	/// 
	#[must_use]
	pub fn checked_add(self, rhs: Self) -> Option<Self> {
		self.0.checked_add(rhs.0).and_then(|v| (v <= Self::MAX.0).then_some(Self(v)))
	}
	
	//		checked_div															
	/// Checked division.
	/// 
	/// Computes `self / rhs`, returning [`None`] if `rhs` is zero or the result
	/// is too large to fit in a [`u63`].
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[must_use]
	pub fn checked_div(self, rhs: Self) -> Option<Self> {
		if rhs.0 == 0 {
			None
		} else {
			self.0.checked_div(rhs.0).map(Self)
		}
	}
	
	//		checked_mul															
	/// Checked multiplication.
	/// 
	/// Computes `self * rhs`, returning [`None`] if overflow occurred.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to multiply `self` by.
	/// 
	#[must_use]
	pub fn checked_mul(self, rhs: Self) -> Option<Self> {
		self.0.checked_mul(rhs.0).and_then(|v| (v <= Self::MAX.0).then_some(Self(v)))
	}
	
	//		checked_pow															
	/// Checked exponentiation.
	/// 
	/// Computes `self.pow(rhs)`, returning [`None`] if the result is too large
	/// to fit in a [`u63`].
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to raise `self` to.
	/// 
	#[must_use]
	pub fn checked_pow(self, rhs: u32) -> Option<Self> {
		self.0.checked_pow(rhs).and_then(|v| (v <= Self::MAX.0).then_some(Self(v)))
	}
	
	//		checked_rem															
	/// Checked remainder.
	/// 
	/// Computes `self % rhs`, returning [`None`] if `rhs` is zero or the result
	/// is too large to fit in a [`u63`].
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[must_use]
	pub fn checked_rem(self, rhs: Self) -> Option<Self> {
		if rhs.0 == 0 {
			None
		} else {
			self.0.checked_rem(rhs.0).map(Self)
		}
	}
	
	//		checked_sub															
	/// Checked subtraction.
	/// 
	/// Computes `self - rhs`, returning [`None`] if overflow occurred.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to subtract from `self`.
	/// 
	#[must_use]
	pub fn checked_sub(self, rhs: Self) -> Option<Self> {
		self.0.checked_sub(rhs.0).map(Self)
	}
	
	//		count_ones															
	/// Counts the number of ones in the binary representation of the value.
	#[must_use]
	pub const fn count_ones(self) -> u32 {
		self.0.count_ones()
	}
	
	//		count_zeroes														
	/// Counts the number of zeroes in the binary representation of the value.
	#[must_use]
	pub const fn count_zeros(self) -> u32 {
		//	Mask with MAX to ignore highest bit
		(self.0 & Self::MAX.0).count_zeros().saturating_sub(1)
	}
	
	//		is_power_of_two														
	/// Determines if the value is a power of two.
	#[must_use]
	pub const fn is_power_of_two(self) -> bool {
		self.0.is_power_of_two()
	}
	
	//		leading_ones														
	/// Counts the number of leading ones in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is the number of bits in the value.
	/// 
	#[must_use]
	pub const fn leading_ones(self) -> u32 {
		(self.0 << 1).leading_ones()
	}
	
	//		leading_zeros														
	/// Counts the number of leading zeroes in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is the number of bits in the value.
	/// 
	#[must_use]
	pub const fn leading_zeros(self) -> u32 {
		(self.0 << 1 | Self::MASK_TRAILING).leading_zeros()
	}
	
	//		overflowing_add														
	/// Overflowing addition.
	/// 
	/// Computes `self + rhs`, returning a tuple of the result and a boolean
	/// indicating whether an arithmetic overflow would occur.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to add to `self`.
	/// 
	#[must_use]
	pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
		let (value, overflow1) = self.0.overflowing_add(rhs.0);
		let overflow2 = value > Self::MAX.0;
		(Self(value & Self::MAX.0), overflow1 || overflow2)
	}
	
	//		overflowing_div														
	/// Overflowing division.
	/// 
	/// Computes `self / rhs`, returning a tuple of the result and a boolean
	/// indicating whether an arithmetic overflow would occur.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[must_use]
	pub const fn overflowing_div(self, rhs: Self) -> (Self, bool) {
		if rhs.0 == 0 {
			(Self::MAX, true)
		} else {
			let (value, overflow) = self.0.overflowing_div(rhs.0);
			(Self(value), overflow)
		}
	}
	
	//		overflowing_mul														
	/// Overflowing multiplication.
	/// 
	/// Computes `self * rhs`, returning a tuple of the result and a boolean
	/// indicating whether an arithmetic overflow would occur.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to multiply `self` by.
	/// 
	#[must_use]
	pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
		let (value, overflow1) = self.0.overflowing_mul(rhs.0);
		let overflow2 = value > Self::MAX.0;
		(Self(value & Self::MAX.0), overflow1 || overflow2)
	}
	
	//		overflowing_pow														
	/// Overflowing exponentiation.
	/// 
	/// Computes `self.pow(rhs)`, returning a tuple of the result and a boolean
	/// indicating whether an arithmetic overflow would occur.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to raise `self` to.
	/// 
	#[must_use]
	pub const fn overflowing_pow(self, rhs: u32) -> (Self, bool) {
		let (value, overflow1) = self.0.overflowing_pow(rhs);
		let overflow2 = value > Self::MAX.0;
		(Self(value & Self::MAX.0), overflow1 || overflow2)
	}
	
	//		overflowing_rem														
	/// Overflowing remainder.
	/// 
	/// Computes `self % rhs`, returning a tuple of the result and a boolean
	/// indicating whether an arithmetic overflow would occur.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[must_use]
	pub const fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
		if rhs.0 == 0 {
			(Self::MAX, true)
		} else {
			let (value, overflow) = self.0.overflowing_rem(rhs.0);
			(Self(value), overflow)
		}
	}
	
	//		overflowing_sub														
	/// Overflowing subtraction.
	/// 
	/// Computes `self - rhs`, returning a tuple of the result and a boolean
	/// indicating whether an arithmetic overflow would occur.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to subtract from `self`.
	/// 
	#[must_use]
	pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
		let (value, overflow) = self.0.overflowing_sub(rhs.0);
		(Self(value & Self::MAX.0), overflow)
	}
	
	//		reverse_bits														
	/// Reverses the bits of the value.
	/// 
	/// The least-significant bit becomes the most-significant bit and vice
	/// versa.
	/// 
	#[must_use]
	pub const fn reverse_bits(self) -> Self {
		//	Shift right after reversal to clear highest bit
		Self(self.0.reverse_bits() >> 1)
	}
	
	//		rotate_left															
	/// Rotates the bits of the value to the left.
	/// 
	/// The `n` most-significant bits are moved to the `n` least-significant
	/// bits, and the rest are moved to the left.
	/// 
	/// # Parameters
	/// 
	/// * `n` - The number of bits to rotate by.
	/// 
	#[must_use]
	pub const fn rotate_left(self, n: u32) -> Self {
		//	Normalize rotation to within 63 bits
		let bits = n % 63;
		Self((self.0 << bits | self.0 >> (63_u32.saturating_sub(bits))) & Self::MAX.0)
	}
	
	//		rotate_right														
	/// Rotates the bits of the value to the right.
	/// 
	/// The `n` least-significant bits are moved to the `n` most-significant
	/// bits, and the rest are moved to the right.
	/// 
	/// # Parameters
	/// 
	/// * `n` - The number of bits to rotate by.
	/// 
	#[must_use]
	pub const fn rotate_right(self, n: u32) -> Self {
		//	Normalize rotation to within 63 bits
		let bits = n % 63;
		Self((self.0 >> bits | self.0 << (63_u32.saturating_sub(bits))) & Self::MAX.0)
	}
	
	//		saturating_add														
	/// Saturating addition.
	/// 
	/// Computes `self + rhs`, saturating at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to add to `self`.
	/// 
	#[must_use]
	pub fn saturating_add(self, rhs: Self) -> Self {
		Self(self.0.saturating_add(rhs.0).min(Self::MAX.0))
	}
	
	//		saturating_div														
	/// Saturating division.
	/// 
	/// Computes `self / rhs`, saturating at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	#[must_use]
	pub const fn saturating_div(self, rhs: Self) -> Self {
		if rhs.0 == 0 {
			Self::MAX
		} else {
			Self(self.0.saturating_div(rhs.0))
		}
	}
	
	//		saturating_mul														
	/// Saturating multiplication.
	/// 
	/// Computes `self * rhs`, saturating at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to multiply `self` by.
	/// 
	#[must_use]
	pub fn saturating_mul(self, rhs: Self) -> Self {
		Self(self.0.saturating_mul(rhs.0).min(Self::MAX.0))
	}
	
	//		saturating_pow														
	/// Saturating exponentiation.
	/// 
	/// Computes `self.pow(rhs)`, saturating at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to raise `self` to.
	/// 
	#[must_use]
	pub fn saturating_pow(self, rhs: u32) -> Self {
		Self(self.0.saturating_pow(rhs).min(Self::MAX.0))
	}
	
	//		saturating_sub														
	/// Saturating subtraction.
	/// 
	/// Computes `self - rhs`, saturating at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to subtract from `self`.
	/// 
	#[must_use]
	pub const fn saturating_sub(self, rhs: Self) -> Self {
		Self(self.0.saturating_sub(rhs.0))
	}
	
	//		trailing_ones														
	/// Counts the number of trailing ones in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is zero.
	/// 
	#[must_use]
	pub const fn trailing_ones(self) -> u32 {
		(self.0 & Self::MAX.0).trailing_ones()
	}
	
	//		trailing_zeros														
	/// Counts the number of trailing zeroes in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is the number of bits in the value.
	/// 
	#[must_use]
	pub const fn trailing_zeros(self) -> u32 {
		(self.0 | Self::MASK_LEADING).trailing_zeros()
	}
	
	//		wrapping_add														
	/// Wrapping addition.
	/// 
	/// Computes `self + rhs`, wrapping around at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to add to `self`.
	/// 
	#[must_use]
	pub const fn wrapping_add(self, rhs: Self) -> Self {
		let (value, _) = self.0.overflowing_add(rhs.0);
		//	Mask off the highest bit to keep in range
		Self(value & Self::MAX.0)
	}
	
	//		wrapping_div														
	/// Wrapping division.
	/// 
	/// Computes `self / rhs`, wrapping around at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	#[must_use]
	pub const fn wrapping_div(self, rhs: Self) -> Self {
		if rhs.0 == 0 {
			Self::MAX
		} else {
			Self(self.0.wrapping_div(rhs.0))
		}
	}
	
	//		wrapping_mul														
	/// Wrapping multiplication.
	/// 
	/// Computes `self * rhs`, wrapping around at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to multiply `self` by.
	/// 
	#[must_use]
	pub const fn wrapping_mul(self, rhs: Self) -> Self {
		let (value, _) = self.0.overflowing_mul(rhs.0);
		//	Mask off the highest bit to keep in range
		Self(value & Self::MAX.0)
	}
	
	//		wrapping_pow														
	/// Wrapping exponentiation.
	/// 
	/// Computes `self.pow(rhs)`, wrapping around at the numeric bounds instead
	/// of overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to raise `self` to.
	/// 
	#[must_use]
	pub const fn wrapping_pow(self, rhs: u32) -> Self {
		let (value, _) = self.0.overflowing_pow(rhs);
		//	Mask off the highest bit to keep in range
		Self(value & Self::MAX.0)
	}
	
	//		wrapping_rem														
	/// Wrapping remainder.
	/// 
	/// Computes `self % rhs`, wrapping around at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	#[must_use]
	pub const fn wrapping_rem(self, rhs: Self) -> Self {
		if rhs.0 == 0 {
			Self::MAX
		} else {
			Self(self.0.wrapping_rem(rhs.0))
		}
	}
	
	//		wrapping_sub														
	/// Wrapping subtraction.
	/// 
	/// Computes `self - rhs`, wrapping around at the numeric bounds instead of
	/// overflowing.
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to subtract from `self`.
	/// 
	#[must_use]
	pub const fn wrapping_sub(self, rhs: Self) -> Self {
		Self(self.0.wrapping_sub(rhs.0) & Self::MAX.0)
	}
}

//󰭅		Add																		
impl Add for u63 {
	type Output = Self;
	
	//		add																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn add(self, rhs: Self) -> Self::Output {
		self.checked_add(rhs).expect("Attempt to add overflowed")
	}
}

//󰭅		AddAssign																
impl AddAssign for u63 {
	//		add_assign															
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn add_assign(&mut self, rhs: Self) {
		*self = *self + rhs;
	}
}

//󰭅		Binary																	
impl Binary for u63 {
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0b")?;
		}
		write!(f, "{:b}", self.0)
	}
}

//󰭅		BitAnd																	
impl BitAnd for u63 {
	type Output = Self;
	
	//		bitand																
	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

//󰭅		BitAndAssign															
impl BitAndAssign for u63 {
	//		bitand_assign														
	fn bitand_assign(&mut self, rhs: Self) {
		*self = *self & rhs;
	}
}

//󰭅		BitOr																	
impl BitOr for u63 {
	type Output = Self;
	
	//		bitor																
	fn bitor(self, rhs: Self) -> Self::Output {
		Self(self.0 | rhs.0)
	}
}

//󰭅		BitOrAssign																
impl BitOrAssign for u63 {
	//		bitor_assign														
	fn bitor_assign(&mut self, rhs: Self) {
		*self = *self | rhs;
	}
}

//󰭅		BitXor																	
impl BitXor for u63 {
	type Output = Self;
	
	//		bitxor																
	fn bitxor(self, rhs: Self) -> Self::Output {
		Self(self.0 ^ rhs.0)
	}
}

//󰭅		BitXorAssign															
impl BitXorAssign for u63 {
	//		bitxor_assign														
	fn bitxor_assign(&mut self, rhs: Self) {
		*self = *self ^ rhs;
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
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn div(self, rhs: Self) -> Self::Output {
		assert_ne!(rhs.0, 0, "Attempt to divide by zero");
		self.checked_div(rhs).expect("Attempt to divide overflowed")
	}
}

//󰭅		DivAssign																
impl DivAssign for u63 {
	//		div_assign															
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn div_assign(&mut self, rhs: Self) {
		*self = *self / rhs;
	}
}

//󰭅		From: u8 -> u63															
impl From<u8> for u63 {
	//		from																
	fn from(v: u8) -> Self {
		#[expect(clippy::cast_lossless, reason = "Fine here")]
		Self(v as u64)
	}
}

//󰭅		From: u16 -> u63														
impl From<u16> for u63 {
	//		from																
	fn from(v: u16) -> Self {
		#[expect(clippy::cast_lossless, reason = "Fine here")]
		Self(v as u64)
	}
}

//󰭅		From: u32 -> u63														
impl From<u32> for u63 {
	//		from																
	fn from(v: u32) -> Self {
		#[expect(clippy::cast_lossless, reason = "Fine here")]
		Self(v as u64)
	}
}

//󰭅		From: u63 -> i64														
impl From<u63> for i64 {
	//		from																
	#[expect(clippy::cast_possible_wrap, reason = "Safe, as fully managed")]
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

//󰭅		FromStr																	
impl FromStr for u63 {
	type Err = ConversionError;
	
	//		from_str															
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		u64::from_str(s).map_err(Into::into).and_then(Self::new)
	}
}

//󰭅		LowerExp																
impl LowerExp for u63 {
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		write!(f, "{:e}", self.0)
	}
}

//󰭅		LowerHex																
impl LowerHex for u63 {
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0x")?;
		}
		write!(f, "{:x}", self.0)
	}
}

//󰭅		Mul																		
impl Mul for u63 {
	type Output = Self;
	
	//		mul																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn mul(self, rhs: Self) -> Self::Output {
		self.checked_mul(rhs).expect("Attempt to multiply overflowed")
	}
}

//󰭅		MulAssign																
impl MulAssign for u63 {
	//		mul_assign															
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn mul_assign(&mut self, rhs: Self) {
		*self = *self * rhs;
	}
}

//󰭅		Not																		
impl Not for u63 {
	type Output = Self;
	
	//		not																	
	fn not(self) -> Self::Output {
		Self(!self.0 & Self::MAX.0)
	}
}

//󰭅		Octal																	
impl Octal for u63 {
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0o")?;
		}
		write!(f, "{:o}", self.0)
	}
}

//󰭅		Product																	
impl Product for u63 {
	//		product																
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn product<I>(iter: I) -> Self
	where
		I: Iterator<Item = Self>,
	{
		iter.fold(Self(1), |acc, x| acc * x)
	}
}

//󰭅		Product<&>																
impl<'a> Product<&'a Self> for u63 {
	//		product																
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn product<I>(iter: I) -> Self
	where
		I: Iterator<Item = &'a Self>,
	{
		iter.fold(Self(1), |acc, &x| acc * x)
	}
}

//󰭅		Rem																		
impl Rem for u63 {
	type Output = Self;
	
	//		rem																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn rem(self, rhs: Self) -> Self::Output {
		assert_ne!(rhs.0, 0, "Attempt to calculate remainder with a divisor of zero");
		self.checked_rem(rhs).expect("Attempt to calculate remainder overflowed")
	}
}

//󰭅		RemAssign																
impl RemAssign for u63 {
	//		rem_assign															
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn rem_assign(&mut self, rhs: Self) {
		*self = *self % rhs;
	}
}

//󰭅		Shl																		
impl Shl<u32> for u63 {
	type Output = Self;
	
	//		shl																	
	fn shl(self, rhs: u32) -> Self::Output {
		Self((self.0 << (rhs % 64)) & Self::MAX.0)
	}
}

//󰭅		ShlAssign																
impl ShlAssign<u32> for u63 {
	//		shl_assign															
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn shl_assign(&mut self, rhs: u32) {
		*self = *self << rhs;
	}
}

//󰭅		Shr																		
impl Shr<u32> for u63 {
	type Output = Self;
	
	//		shr																	
	fn shr(self, rhs: u32) -> Self::Output {
		Self(self.0 >> (rhs % 64))
	}
}

//󰭅		ShrAssign																
impl ShrAssign<u32> for u63 {
	//		shr_assign															
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn shr_assign(&mut self, rhs: u32) {
		*self = *self >> rhs;
	}
}

//󰭅		Sub																		
impl Sub for u63 {
	type Output = Self;
	
	//		sub																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn sub(self, rhs: Self) -> Self::Output {
		self.checked_sub(rhs).expect("Attempt to subtract overflowed")
	}
}

//󰭅		SubAssign																
impl SubAssign for u63 {
	//		sub_assign															
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn sub_assign(&mut self, rhs: Self) {
		*self = *self - rhs;
	}
}

//󰭅		Sum																		
impl Sum for u63 {
	//		sum																	
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn sum<I>(iter: I) -> Self
	where
		I: Iterator<Item = Self>,
	{
		iter.fold(Self::MIN, |acc, x| acc + x)
	}
}

//󰭅		Sum<&>																	
impl<'a> Sum<&'a Self> for u63 {
	//		sum																	
	#[expect(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]
	fn sum<I>(iter: I) -> Self
	where
		I: Iterator<Item = &'a Self>,
	{
		iter.fold(Self::MIN, |acc, &x| acc + x)
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
		#[expect(clippy::cast_lossless, reason = "Fine here")]
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: i16 -> u63														
impl TryFrom<i16> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i16) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_lossless, reason = "Fine here")]
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: i32 -> u63														
impl TryFrom<i32> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i32) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_lossless, reason = "Fine here")]
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: i64 -> u63														
impl TryFrom<i64> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i64) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_sign_loss, reason = "Already checked")]
		(v >= 0).then_some(Self(v as u64)).ok_or(ConversionError::ValueIsNegative)
	}
}

//󰭅		TryFrom: i128 -> u63													
impl TryFrom<i128> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i128) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_lossless, reason = "Fine here")]
		if v < 0 {
			Err(ConversionError::ValueIsNegative)
		} else if v > i64::MAX as i128 {
			Err(ConversionError::ValueTooLarge)
		} else {
			#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
			#[expect(clippy::cast_sign_loss,           reason = "Already checked")]
			Ok(Self(v as u64))
		}
	}
}

//󰭅		TryFrom: isize -> u63													
impl TryFrom<isize> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: isize) -> Result<Self, Self::Error> {
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: u63 -> i8														
impl TryFrom<u63> for i8 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> i16														
impl TryFrom<u63> for i16 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> i32														
impl TryFrom<u63> for i32 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> isize													
impl TryFrom<u63> for isize {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		Ok(Self::try_from(v.as_i64())?)
	}
}

//󰭅		TryFrom: u63 -> u8														
impl TryFrom<u63> for u8 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_lossless,            reason = "Fine here")]
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> u16														
impl TryFrom<u63> for u16 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_lossless,            reason = "Fine here")]
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> u32														
impl TryFrom<u63> for u32 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_lossless,            reason = "Fine here")]
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
		(v.as_u64() <= Self::MAX as u64).then_some(v.as_u64() as Self).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: u63 -> usize													
impl TryFrom<u63> for usize {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u63) -> Result<Self, Self::Error> {
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
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
		#[expect(clippy::cast_possible_truncation, reason = "Already checked")]
		(v <= i64::MAX as u128).then_some(Self(v as u64)).ok_or(ConversionError::ValueTooLarge)
	}
}

//󰭅		TryFrom: usize -> u63													
impl TryFrom<usize> for u63 {
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: usize) -> Result<Self, Self::Error> {
		Self::try_from(v as u64)
	}
}

//󰭅		UpperExp																
impl UpperExp for u63 {
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		write!(f, "{:E}", self.0)
	}
}

//󰭅		UpperHex																
impl UpperHex for u63 {
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0x")?;
		}
		write!(f, "{:X}", self.0)
	}
}


