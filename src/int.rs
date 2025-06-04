//! Custom variable-length integer type.

//	These lint checks are unnecessary in this module because:
//	  1. We're working with GenericArray where we know the size at compile time.
//	  2. All our indexing is based on the BYTES constant which is tied to the
//	     type's size.
//	  3. Using .get() would add unnecessary runtime checks and make the code
//	     more verbose with .unwrap()s.
//	  4. The indexing operations are fundamentally safe due to the type system
//	     ensuring the arrays are the correct size.
#![allow(
	clippy::indexing_slicing,
	clippy::missing_asserts_for_indexing,
	reason = "We always know the size"
)]

//	This lint check is unnecessary in this module because these arithmetic
//	operations are actually essential parts of our logic. We don't want to add
//	unnecessary checks when we know the operations are safe, or potentially hide
//	actual issues we should catch. We also want to emulate the Rust standard
//	library behaviour.
#![allow(clippy::arithmetic_side_effects, reason = "Needs to emulate Rust standard library behaviour")]



//		Modules																											

#[cfg(test)]
#[path = "tests/int.rs"]
mod tests;



//		Packages																										

use crate::errors::ConversionError;
use bytes::BytesMut;
use core::{
	error::Error,
	fmt::{Binary, Debug, Display, Formatter, LowerExp, LowerHex, Octal, UpperExp, UpperHex, self},
	iter::{Product, Sum},
	marker::PhantomData,
	ops::{Add, AddAssign, Bound, Div, DivAssign, Mul, MulAssign, Neg, RangeBounds, Rem, RemAssign, Sub, SubAssign},
	ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr, ShrAssign},
	str::FromStr,
};
use generic_array::{ArrayLength, GenericArray};
use serde::{
	Deserialize,
	Deserializer,
	Serialize,
	Serializer,
	de::{Error as SerdeError, Visitor},
};
use serde_json::Error as JsonError;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use tokio_postgres::types::{FromSql, IsNull, ToSql, Type, to_sql_checked};
use typenum::{B0, B1, Quot, Sum as TnSum, U7, U8, UInt as TnUInt, Unsigned, UTerm};



//		Type aliases																									

/// Helper type to calculate number of bytes needed for bits.
pub type BytesForBits<BITS> = Quot<TnSum<BITS, U7>, U8>;

/// Type alias for signed integers, for convenience.
pub type SInt<BITS> = Int<BITS, true>;

/// Type alias for unsigned integers, for convenience.
pub type UInt<BITS> = Int<BITS, false>;



//		Structs																											

//		Int																		
/// A flexible-length integer.
/// 
/// This type provides an integer of arbitrary length, and which can be signed
/// or unsigned.
/// 
/// # Type parameters
/// 
/// * `BITS`   - The number of bits used to represent the integer (65,536 max).
/// * `SIGNED` - Whether the integer is signed (`true`) or unsigned (`false`).
/// 
/// # Use cases
/// 
/// ## Database compatibility
/// 
/// This type can be used to create an unsigned 63-bit integer, i.e. `Int<63,
/// false>` (or `Uint<63>`), to represent the crossover between a [`u64`] (which
/// would be the choice for the types used in Rust) and an [`i64`] (which is a
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
/// Therefore this type is a good choice to use because we want an unsigned
/// integer with the maximum range possible.
/// 
/// ## Efficiency
/// 
/// This type is also useful for efficiency, as it can be used to create
/// integers that only take the space they need between the standard sizes, e.g.
/// 24-bit, 48-bit, etc.
/// 
/// ## Higher boundaries
/// 
/// This type can also be used to create integers with higher boundaries than
/// the standard Rust integer types, e.g. 256-bit, 512-bit, etc. all the way up
/// to 65,536-bit (note that this is achieved by setting the `BITS` constant to
/// zero). This is still within the technical range Rust allows for [`Copy`],
/// but sets a sensible limit.
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
/// Note that, for now at least, only [`Int`]s of the same bit length and sign
/// can be used together in arithmetic operations.
/// 
/// # Conversion
/// 
/// This type can be converted to and from any of the following types:
/// 
///   - [`i8`], [`i16`], [`i32`], [`i64`], [`i128`], [`isize`]
///   - [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], [`usize`]
/// 
/// As all the conversions are potentially lossy, [`TryFrom`] is implemented
/// universally, and there are no [`From`] implementations for the types above.
/// 
/// # Performance
/// 
/// The primary utility of this type is for supporting particular limits, for
/// reasons of compatibility, efficiency, and higher boundaries. It is not going
/// to be as fast as the standard integer types, and — for now at least — the
/// arithmetic operations are accurate but not optimised for speed.
/// 
/// In future various aspects of performance may be improved, for instance by
/// introducing SIMD optimisations, but this is not a priority at present.
/// 
/// # Types
/// 
/// The internal type uses [`GenericArray`] in combination with [`typenum`] for
/// calculations, which is necessary for now until Rust adds support for generic
/// parameters being used in const operations, at which point it can change to a
/// fixed-size byte array. We ideally want to do something like `[u8; { (BITS as
/// usize + 7) / 8 }]` but this is not yet possible. Therefore, the best
/// compromise at present is a `GenericArray<u8, BytesForBits<N>>`, which
/// supports [`Copy`] (unlike [`Vec`]), and allows the length to be set at
/// compile time. It is therefore very similar to the ideal, but does require
/// the bit width to be set using [`typenum`] types.
/// 
/// This itself means that instead of `Int<const BITS: u16, const SIGNED: bool>`
/// we need to use `Int<N, const SIGNED: bool>`, where `N` is a [`typenum`] type
/// representing the number of bits. In actual usage this means writing e.g.
/// `Int<U47, true>` instead of just `Int<47, true>` — the difference is
/// somewhat minimal, but does involve loading in the type, or creating it if it
/// does not exist.
/// 
/// [`typenum`] offers a range of standard-sized integer types, but it also
/// allows creation of custom types, which is necessary if using a bit width
/// that is not a standard [`typenum`] integer. For instance, for 60,000 bits,
/// `Prod<U300, U200>` can be used, and then assigned to a type, e.g. `type
/// U60000 = Prod<U300, U200>`. Using that in an [`Int`] would then look like
/// `Int<U60000, false>`.
/// 
/// However, the performance and memory usage of [`GenericArray`] will be
/// essentially identical to a fixed-size byte array, so at least this is not a
/// concern in the meantime.
/// 
/// # Internal representation
/// 
/// The value is stored as a sequence of bytes in little-endian order (least
/// significant byte first). This matches the most common CPU architectures and
/// Rust's internal representation of primitive integers.
/// 
/// For example, the 16-bit value `0x1234`:
/// 
///   - Written in hex: `0x1234` (most-significant bytes written first by
///     convention)
///   - Stored in memory: `[0x34, 0x12]` (least-significant byte stored first)
/// 
/// Within each byte, bits are ordered from least significant (bit 0) to most
/// significant (bit 7), again matching CPU architecture and Rust conventions.
/// This means that bit operations (like [`bit()`](Int::bit()),
/// [`set_bit()`](Int::set_bit()), and [`bits()`](Int::bits())) use zero-based
/// indices where bit 0 is the least-significant bit of the first byte, bit 8 is
/// the least-significant bit of the second byte, and so on.
/// 
/// Example bit layout:
/// 
/// ```text
/// Value:     0x1234
/// In memory: [0x34, 0x12]
/// 
/// Byte 0:    0011 0100  (bits 0-7)   LSB
/// Byte 1:    0001 0010  (bits 8-15)  MSB
/// ```
/// 
/// All operations maintain this layout, ensuring consistent behavior across
/// platforms and compatibility with Rust's primitive integer types. Conversion
/// methods that deal with raw bytes (like [`to_le_bytes()`](Int::to_le_bytes())
/// and [`to_be_bytes()`](Int::to_be_bytes())) handle any necessary byte
/// reordering explicitly.
/// 
#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Int<BITS, const SIGNED: bool>(GenericArray<u8, BytesForBits<BITS>>)
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
;

//󰭅		Int																		
impl<BITS, const SIGNED: bool> Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		Public constants													
	/// Number of bits used for storage. This is a 16-bit value, allowing for up
	/// to 65,536 bits in total.
	pub const BITS:  u16 = BITS::U16;
	
	/// Number of bytes used for storage. Although it is a 16-bit value, the
	/// maximum number of bytes is 8,192, which is the maximum number of bits
	/// (65,536) divided by 8.
	pub const BYTES: u16 = BytesForBits::<BITS>::U16;
	
	//		Private constants													
	/// Mask for valid bits in the last byte.
	#[expect(
		clippy::cast_possible_truncation,
		reason = "Value is at most 255 after shift of at most 7 bits and subtraction of 1"
	)]
	const LAST_BYTE_MASK: u8 = {
		let bits = Self::BITS;
		if bits % 8 == 0 {
			0xFF
		} else {
			let shift = bits % 8;
			//	Safe conversion after shift
			((1_u16 << shift) - 1) as u8
		}
	};
	
	/// Position of the sign bit within the last byte.
	const SIGN_BIT_POS: u8 = {
		let bits = Self::BITS;
		//	Safely get position within byte (0-7)
		((bits - 1) & 0x7) as u8
	};
	
	//		Constructors														
	
	//		new																	
	/// Creates a new [`Int`] from bytes.
	/// 
	/// # Parameters
	/// 
	/// * `value` - The value to create the [`Int`] from.
	/// 
	/// # Errors
	/// 
	/// Returns an error if the value is too large to fit in an [`Int`].
	/// 
	pub fn new(bytes: GenericArray<u8, BytesForBits<BITS>>) -> Result<Self, ConversionError> {
		//	Create a copy we can modify to check validity
		let mut value = bytes;
		
		if SIGNED {
			//	For signed numbers, check if sign bit matches padding bits
			let sign_bit = (value[Self::BYTES as usize - 1] >> ((Self::BITS - 1) % 8)) & 1;
			let expected_padding = if sign_bit == 1 { 0xFF } else { 0 };
			
			//	Check padding bits in last byte
			let last_byte_padding = value[Self::BYTES as usize - 1] & !Self::LAST_BYTE_MASK;
			if last_byte_padding != expected_padding & !Self::LAST_BYTE_MASK {
				return Err(ConversionError::ValueTooLarge);
			}
		} else {
			//	For unsigned numbers, check all padding bits are zero
			if (value[Self::BYTES as usize - 1] & !Self::LAST_BYTE_MASK) != 0 {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		//	Clear any padding bits in last byte
		value[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Ok(Self(value))
	}
	
	//		Public methods														
	
	//		as_array															
	/// Represents the internal value as a [`GenericArray`] of bytes.
	/// 
	/// This mirrors the internal storage and encompasses length information at
	/// compile time via the type system. This is useful when you need to
	/// preserve the exact size information or work with [`GenericArray`].
	/// 
	#[must_use]
	pub const fn as_array(&self) -> &GenericArray::<u8, BytesForBits<BITS>> {
		&self.0
	}
	
	//		as_slice															
	/// Represents the internal value as a slice of bytes.
	/// 
	/// Returns a standard slice that can be used when needing to work with byte
	/// slices. While the length cannot currently be part of the type signature,
	/// it will always be equal to [`Self::BYTES`].
	/// 
	#[must_use]
	pub const fn as_slice(&self) -> &[u8] {
		self.0.as_slice()
	}
	
	//		bit																	
	/// Gets the value of a specific bit.
	/// 
	/// Returns `false` if the position is out of range.
	/// 
	/// # Parameters
	/// 
	/// * `pos` - The position of the bit to get, where `0` is the
	///           least-significant bit.
	/// 
	#[expect(clippy::integer_division, reason = "Precision is not needed here")]
	pub fn bit(self, pos: u16) -> bool {
		if pos >= Self::BITS {
			return false;
		}
		(self.0[(pos / 8) as usize] & (1 << (pos % 8))) != 0
	}
	
	//		bits																
	/// Returns the bits in the specified range as a [`Vec`] of booleans.
	/// 
	/// Returns an empty [`Vec`] if the range is invalid or out of bounds.
	/// 
	/// # Parameters
	/// 
	/// * `range` - The range of bits to get, where `0` is the least-significant
	///             bit. The range is end-exclusive, like all Rust ranges.
	/// 
	#[must_use]
	pub fn bits<R: RangeBounds<u16>>(&self, range: R) -> Vec<bool> {
		let start = match range.start_bound() {
			Bound::Included(&n) => n,
			Bound::Excluded(&n) => n + 1,
			Bound::Unbounded    => 0,
		};
		let end   = match range.end_bound() {
			Bound::Included(&n) => n + 1,
			Bound::Excluded(&n) => n,
			Bound::Unbounded    => Self::BITS,
		};
		
		if start >= Self::BITS || end > Self::BITS || start >= end {
			return Vec::new();
		}
		
		let mut result = Vec::with_capacity((end - start) as usize);
		for pos in start..end {
			result.push(self.bit(pos));
		}
		result
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
		//	For unsigned numbers, check for overflow up front
		if !SIGNED {
			//	If either number has any bits set beyond what we can represent, 
			//	the result will overflow
			let max = Self::max_value();
			if (max - rhs) < self {
				return None;
			}
		}
		
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		let mut carry  = 0_u8;
		
		//	Add bytes with carry
		for i in 0..Self::BYTES as usize {
			let (sum1, c1) = self.0[i].overflowing_add(rhs.0[i]);
			let (sum2, c2) = sum1.overflowing_add(carry);
			result[i]      = sum2;
			carry          = u8::from(c1 || c2);
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		//	Check for sign-based overflow
		if SIGNED {
			//	Get sign bits
			let a_sign = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			let b_sign = ( rhs.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			let r_sign = (result[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			
			//	Overflow if:
			//	  - Adding two positives gives negative
			//	  - Adding two negatives gives positive
			//	  - Carry propagates into sign bit
			if  (a_sign == 0 && b_sign == 0 && r_sign == 1) ||
				(a_sign == 1 && b_sign == 1 && r_sign == 0) ||
				carry != 0
			{
				None
			} else {
				Some(Self(result))
			}
		} else if carry != 0 {
			None
		} else {
			Some(Self(result))
		}
	}
	
	//		checked_div															
	/// Checked division.
	/// 
	/// Computes `self / rhs`, returning [`None`] if `rhs` is zero or the result
	/// is too large to fit in an [`Int`].
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[must_use]
	pub fn checked_div(self, rhs: Self) -> Option<Self> {
		//	Handle division by zero
		if rhs.is_zero() {
			return None;
		}
		
		//	Handle special cases for signed numbers
		if SIGNED {
			//	Check for overflow: MIN / -1
			if self == Self::min_value() && rhs == -Self::one() {
				return None;
			}
			
			//	Get absolute values and track sign
			let (dividend, neg_dividend) = if self.is_negative() { (-self, true) } else { (self, false) };
			let (abs_rhs, neg_rhs)       = if  rhs.is_negative() { (-rhs,  true) } else { (rhs,  false) };
			//	Result will be negative if signs differ
			let result_negative          = neg_dividend != neg_rhs;
			//	Perform unsigned division on absolute values
			let mut quotient             = Self::zero();
			let mut remainder            = Self::zero();
			
			//	Find highest set bit in divisor
			for i in (0..Self::BITS).rev() {
				if (abs_rhs >> u32::from(i)).is_zero() {
					continue;
				}
				break;
			}
			
			//	Process one bit at a time
			for i in (0..Self::BITS).rev() {
				//	Shift remainder left by 1 and add next bit of dividend
				remainder <<= 1;
				if (dividend >> u32::from(i)).bit(0) {
					remainder |= Self::one();
				}
				
				//	If remainder >= abs_rhs, subtract and set quotient bit
				if remainder >= abs_rhs {
					remainder -= abs_rhs;
					quotient  |= Self::one() << u32::from(i);
				}
			}
			
			//	Apply sign to result
			if result_negative {
				quotient = -quotient;
			}
			
			Some(quotient)
		} else {
			//	Unsigned division is simpler
			let mut quotient  = Self::zero();
			let mut remainder = Self::zero();
			
			//	Find highest set bit in divisor
			for i in (0..Self::BITS).rev() {
				if (rhs >> u32::from(i)).is_zero() {
					continue;
				}
				break;
			}
			
			//	Process one bit at a time
			for i in (0..Self::BITS).rev() {
				//	Shift remainder left by 1 and add next bit of dividend
				remainder <<= 1;
				if (self >> u32::from(i)).bit(0) {
					remainder |= Self::one();
				}
				
				//	If remainder >= rhs, subtract and set quotient bit
				if remainder >= rhs {
					remainder -= rhs;
					quotient  |= Self::one() << u32::from(i);
				}
			}
			
			Some(quotient)
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
		//	Early check for multiplying by zero
		if self.is_zero() || rhs.is_zero() {
			return Some(Self::zero());
		}
		
		//	Early check for multiplying by one
		if rhs == Self::one() {
			return Some(self);
		} else if self == Self::one() {
			return Some(rhs);
		}
		
		//	For unsigned numbers, check for overflow up front
		//	If rhs > max_value / self, we'll overflow
		//	Special case: multiplying by 1 should never overflow
		if !SIGNED && !self.is_zero() && rhs != Self::one() && rhs > Self::max_value() / self {
			return None;
		}
		
		let mut result   = GenericArray::<u8, BytesForBits<BITS>>::default();
		let mut overflow = false;
		
		//	For each byte of self
		for i in 0..Self::BYTES as usize {
			let mut carry = 0_u16;
			
			//	Multiply this byte by each byte of rhs
			for j in 0..Self::BYTES as usize {
				if i + j >= Self::BYTES as usize {
					if carry != 0 || self.0[i] != 0 || rhs.0[j] != 0 {
						overflow = true;
					}
					break;
				}
				
				//	Multiply bytes and add carry
				#[expect(
					clippy::cast_possible_truncation,
					reason = "Lower 8 bits used for result, upper bits captured in carry"
				)]
				{
					let prod      = u16::from(self.0[i]) * u16::from(rhs.0[j]) + carry + u16::from(result[i + j]);
					result[i + j] = prod as u8;
					carry         = prod >> 8_i32;
				}
			}
			
			if carry != 0 {
				overflow = true;
			}
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		//	Check for sign-based overflow
		if SIGNED {
			let a_sign = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			let b_sign = ( rhs.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			let r_sign = (result[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			
			//	Result sign should be product of input signs
			if (a_sign ^ b_sign) != r_sign {
				overflow = true;
			}
			
			//	Check for special case: multiplying by -1 with minimum value
			if (self == Self::min_value() && rhs.is_negative()) ||
				(rhs == Self::min_value() && self.is_negative()) {
				overflow = true;
			}
		}
		
		if overflow {
			None
		} else {
			Some(Self(result))
		}
	}
	
	//		checked_pow															
	/// Checked exponentiation.
	/// 
	/// Computes `self.pow(rhs)`, returning [`None`] if the result is too large
	/// to fit in an [`Int`].
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to raise `self` to.
	/// 
	#[must_use]
	pub fn checked_pow(self, rhs: u32) -> Option<Self> {
		//	Handle special cases
		if rhs == 0 {
			return Some(Self::one());
		}
		if self.is_zero() {
			return Some(Self::zero());
		}
		if self == Self::one() {
			return Some(Self::one());
		}
		if rhs == 1 {
			return Some(self);
		}
		
		//	For unsigned numbers, check if exponent would cause overflow
		if !SIGNED && self > Self::one() {
			//	For base 2, we can use direct bit shifting
			if let Ok(two) = Self::try_from(2_u8) {
				if self == two {
					//	For 2^n, shifting by n must be less than BITS to avoid overflow
					if rhs >= u32::from(Self::BITS) {
						return None;
					}
					return Some(Self::one() << rhs);
				}
				//	For other bases, check bit requirements
				let significant_bits = Self::BITS - self.leading_zeros();
				if rhs.saturating_mul(u32::from(significant_bits)) > u32::from(Self::BITS) {
					return None;
				}
			}
		}
		
		//	For signed numbers:
		//	  - If base is negative and exponent is even, result will be positive
		//	  - If base is negative and exponent is odd, result will be negative
		//	  - If base is -1, result is always either 1 or -1
		//	  - If base is 1, result is always 1
		if SIGNED {
			//	Special case: min_value can overflow even when result should be valid
			if self == Self::min_value() {
				if rhs == 1 {
					return Some(self);
				}
				if rhs % 2 == 0 {
					//	Even power of min_value overflows unless result fits
					let max_shift = Self::BITS - 1;
					#[expect(clippy::cast_possible_truncation, reason = "Power shift amount cannot exceed BITS (u16)")]
					if rhs as u16 > max_shift {
						return None;
					}
					return Some(Self::one() << (rhs - 1));
				}
				//	Will overflow
				return None;
			}
			if self == -Self::one() {
				return Some(if rhs % 2 == 0 { Self::one() } else { -Self::one() });
			}
		}
		
		//	For unsigned values or positive signed values
		let mut base   = self;
		let mut exp    = rhs;
		let mut result = Self::one();
		
		while exp > 0 {
			if exp & 1 == 1 {
				result = result.checked_mul(base)?;
			}
			exp >>= 1_i32;
			if exp > 0 {
				base = base.checked_mul(base)?;
			}
		}
		
		Some(result)
	}
	
	//		checked_rem															
	/// Checked remainder.
	/// 
	/// Computes `self % rhs`, returning [`None`] if `rhs` is zero or the result
	/// is too large to fit in an [`Int`].
	/// 
	/// # Parameters
	/// 
	/// * `rhs` - The value to divide `self` by.
	/// 
	#[must_use]
	pub fn checked_rem(self, rhs: Self) -> Option<Self> {
		//	Handle division by zero
		if rhs.is_zero() {
			return None;
		}
		
		//	Handle special cases for signed numbers
		if SIGNED && self == Self::min_value() && rhs == -Self::one() {
			return Some(Self::zero());
		}
		
		//	Use similar algorithm to division but return remainder
		if SIGNED {
			let (dividend, neg_dividend) = if self.is_negative() { (-self, true) } else { (self, false) };
			let (abs_rhs, _)             = if  rhs.is_negative() { (-rhs,  true) } else { (rhs,  false) };
			
			let mut remainder = Self::zero();
			
			//	Process one bit at a time
			for i in (0..Self::BITS).rev() {
				remainder <<= 1;
				if (dividend >> u32::from(i)).bit(0) {
					remainder |= Self::one();
				}
				
				if remainder >= abs_rhs {
					remainder -= abs_rhs;
				}
			}
			
			//	Remainder takes sign of dividend
			if neg_dividend {
				remainder = -remainder;
			}
			
			Some(remainder)
		} else {
			let mut remainder = Self::zero();
			
			//	Process one bit at a time
			for i in (0..Self::BITS).rev() {
				remainder <<= 1;
				if (self >> u32::from(i)).bit(0) {
					remainder |= Self::one();
				}
				
				if remainder >= rhs {
					remainder -= rhs;
				}
			}
			
			Some(remainder)
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
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		let mut borrow = 0_u8;
		
		//	Subtract bytes with borrow
		for i in 0..Self::BYTES as usize {
			let (diff1, b1) = self.0[i].overflowing_sub(rhs.0[i]);
			let (diff2, b2) = diff1.overflowing_sub(borrow);
			result[i]       = diff2;
			borrow          = u8::from(b1 || b2);
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		//	Check for sign-based overflow
		if SIGNED {
			let a_sign = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			let b_sign = ( rhs.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			let r_sign = (result[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			
			//	Overflow if:
			//	  - Positive - negative = negative
			//	  - Negative - positive = positive
			if (a_sign == 0 && b_sign == 1 && r_sign == 1) ||
				(a_sign == 1 && b_sign == 0 && r_sign == 0) {
				None
			} else {
				Some(Self(result))
			}
		} else {
			//	For unsigned, any borrow means we went negative
			if borrow != 0 {
				None
			} else {
				Some(Self(result))
			}
		}
	}
	
	//		count_ones															
	/// Counts the number of ones in the binary representation of the value.
	#[must_use]
	pub fn count_ones(self) -> u32 {
		let mut count = 0;
		
		//	Count all bytes except last
		#[expect(clippy::integer_division, reason = "Precision is not needed here")]
		let full_bytes = (Self::BITS as usize - 1) / 8;
		let mut i = 0;
		while i < full_bytes {
			count += self.0[i].count_ones();
			i     += 1;
		}
		
		//	Handle last byte with mask
		count += (self.0[Self::BYTES as usize - 1] & Self::LAST_BYTE_MASK).count_ones();
		
		count
	}
	
	//		count_zeroes														
	/// Counts the number of zeroes in the binary representation of the value.
	#[must_use]
	pub fn count_zeros(self) -> u32 {
		u32::from(Self::BITS) - self.count_ones()
	}
	
	//		from_be_bytes()														
	/// Creates an [`Int`] from a big-endian byte array.
	/// 
	/// As this type uses little-endian storage internally, this reverses the
	/// bytes before validation.
	/// 
	/// # Parameters
	/// 
	/// * `bytes` - The big-endian byte array to create the [`Int`] from.
	/// 
	/// # Errors
	/// 
	/// Returns an error if the byte array is not the correct length.
	/// 
	pub fn from_be_bytes(bytes: &[u8]) -> Result<Self, ConversionError> {
		if bytes.len() != Self::BYTES as usize {
			return Err(ConversionError::ValueTooLarge);
		}
		
		let mut value = GenericArray::<u8, BytesForBits<BITS>>::default();
		for i in 0..Self::BYTES as usize {
			value[i] = bytes[Self::BYTES as usize - 1 - i];
		}
		
		Self::new(value)
	}
	
	//		from_json															
	/// Deserialises a JSON string into this integer type.
	/// 
	/// # Parameters
	/// 
	/// * `json` - The JSON string to deserialise.
	/// 
	/// # Errors
	/// 
	/// If the JSON string is invalid, or the number inside the JSON is invalid,
	/// then an error will be returned.
	/// 
	pub fn from_json(json: &str) -> Result<Self, JsonError> {
		serde_json::from_str(json)
	}
	
	//		from_le_bytes()														
	/// Creates an [`Int`] from a little-endian byte array.
	/// 
	/// As this type uses little-endian storage internally, this is a direct
    /// validation of the provided bytes.
	/// 
	/// # Parameters
	/// 
	/// * `bytes` - The little-endian byte array to create the [`Int`] from.
	/// 
	/// # Errors
	/// 
	/// Returns an error if the byte array is not the correct length.
	/// 
	pub fn from_le_bytes(bytes: &[u8]) -> Result<Self, ConversionError> {
		if bytes.len() != Self::BYTES as usize {
			return Err(ConversionError::ValueTooLarge);
		}
		
		let mut value = GenericArray::<u8, BytesForBits<BITS>>::default();
		for i in 0..Self::BYTES as usize {
			value[i] = bytes[i];
		}
		
		Self::new(value)
	}
	
	//		into_array()														
	/// Represents the internal value as a [`GenericArray`] of bytes.
	#[must_use]
	pub const fn into_array(self) -> GenericArray<u8, BytesForBits<BITS>> {
		self.0
	}
	
	//		into_vec()															
	/// Represents the internal value as a [`Vec`] of bytes.
	#[must_use]
	pub fn into_vec(self) -> Vec<u8> {
		self.0.into_iter().collect()
	}
	
	//		is_negative															
	/// Determines if the value is negative.
	#[must_use]
	pub fn is_negative(self) -> bool {
		SIGNED && ((self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1) == 1
	}
	
	//		is_power_of_two														
	/// Determines if the value is a power of two.
	#[must_use]
	pub fn is_power_of_two(self) -> bool {
		self.count_ones() == 1
	}
	
	//		is_zero																
	/// Determines if the value is zero.
	#[must_use]
	pub fn is_zero(self) -> bool {
		self.0.iter().all(|&b| b == 0)
	}
	
	//		leading_ones														
	/// Counts the number of leading ones in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is the number of bits in the value.
	/// 
	#[must_use]
	pub fn leading_ones(self) -> u16 {
		let mut count = 0;
		
		//	Start from the highest valid bit (bit 62 for u63) and work down
		for i in (0..Self::BITS).rev() {
			#[expect(clippy::integer_division, reason = "Precision is not needed here")]
			let byte_idx   = (i / 8) as usize;
			let bit_idx    =  i % 8;
			let bit_is_set = (self.0[byte_idx] & (1 << bit_idx)) != 0;
			
			if !bit_is_set {
				break;
			}
			count += 1;
		}
		count
	}
	
	//		leading_zeros														
	/// Counts the number of leading zeroes in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is the number of bits in the value.
	/// 
	#[must_use]
	pub fn leading_zeros(self) -> u16 {
		let mut count = 0;
		
		//	Start from the highest valid bit (bit 62 for u63) and work down
		for i in (0..Self::BITS).rev() {
			#[expect(clippy::integer_division, reason = "Precision is not needed here")]
			let byte_idx   = (i / 8) as usize;
			let bit_idx    =  i % 8;
			let bit_is_set = (self.0[byte_idx] & (1 << bit_idx)) != 0;
			
			if bit_is_set {
				break;
			}
			count += 1;
		}
		count
	}
	
	//		max_value															
	/// The maximum value for an [`Int`].
	/// 
	/// Ideally this would be a constant, but that's not possible just yet until
	/// Rust stabilises const generic expressions.
	/// 
	#[must_use]
	pub fn max_value() -> Self {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		result.iter_mut().for_each(|b| *b = 0xFF);
		let last_idx = result.len() - 1;
		result[last_idx] &= if SIGNED {
			Self::LAST_BYTE_MASK >> 1_i32
		} else {
			Self::LAST_BYTE_MASK
		};
		Self(result)
	}
	
	//		min_value															
	/// The minimum value for an [`Int`].
	/// 
	/// Ideally this would be a constant, but that's not possible just yet until
	/// Rust stabilises const generic expressions.
	/// 
	#[must_use]
	pub fn min_value() -> Self {
		if SIGNED {
			let mut result   = GenericArray::<u8, BytesForBits<BITS>>::default();
			let last_idx     = result.len() - 1;
			result[last_idx] = 1 << Self::SIGN_BIT_POS;
			Self(result)
		} else {
			Self(GenericArray::default())
		}
	}
	
	//		one																	
	/// The value of `1` as an [`Int`].
	/// 
	/// Ideally this would be a constant, but that's not possible just yet until
	/// Rust stabilises const generic expressions.
	/// 
	#[must_use]
	pub fn one() -> Self {
		let mut result = GenericArray::default();
		result[0]      = 1;
		Self(result)
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
	pub fn overflowing_add(self, rhs: Self) -> (Self, bool) {
		self.checked_add(rhs).map_or_else(|| {
			//	On overflow, wrap the result and return true
			let mut result = self.wrapping_add(rhs);
			result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
			(result, true)
 		}, |result| (result, false))
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
	pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
		if rhs.is_zero() {
			//	Division by zero returns max value and true
			return (Self::max_value(), true);
		}
		
		self.checked_div(rhs).map_or_else(|| {
			//	On overflow, wrap the result and return true
			let mut result = self.wrapping_div(rhs);
			result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
			(result, true)
		}, |result| (result, false))
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
	pub fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
		self.checked_mul(rhs).map_or_else(|| {
			//	On overflow, wrap the result and return true
			let mut result = self.wrapping_mul(rhs);
			result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
			(result, true)
		}, |result| (result, false))
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
	pub fn overflowing_pow(self, rhs: u32) -> (Self, bool) {
		self.checked_pow(rhs).map_or_else(|| {
			//	On overflow, wrap the result and return true
			let mut result = self.wrapping_pow(rhs);
			result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
			(result, true)
		}, |result| (result, false))
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
	pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
		if rhs.is_zero() {
			//	Remainder by zero returns max value and true
			return (Self::max_value(), true);
		}
		
		self.checked_rem(rhs).map_or_else(|| {
			//	On overflow, wrap the result and return true
			let mut result = self.wrapping_rem(rhs);
			result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
			(result, true)
		}, |result| (result, false))
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
	pub fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
		self.checked_sub(rhs).map_or_else(|| {
			//	On overflow, wrap the result and return true
			let mut result = self.wrapping_sub(rhs);
			result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
			(result, true)
		}, |result| (result, false))
	}
	
	//		parse																
	/// Parses a string slice into an integer.
	/// 
	/// The string can be in various formats:
	/// 
	///   - Decimal (no prefix)
	///   - Hexadecimal (`0x` prefix)
	///   - Binary (`0b` prefix)
	///   - Octal (`0o` prefix)
	/// 
	/// For signed types, an optional `+` or `-` prefix is allowed.
	/// 
	/// Underscores between digits are allowed and ignored.
	/// 
	/// # Parameters
	/// 
	/// * `s` - The string to parse.
	/// 
	/// # Errors
	/// 
	/// If the number is invalid, an error will be returned.
	/// 
	pub fn parse(s: &str) -> Result<Self, ConversionError> {
		s.parse()
	}
	
	//		reverse_bits														
	/// Reverses the bits of the value.
	/// 
	/// The least-significant bit becomes the most-significant bit and vice
	/// versa.
	/// 
	#[must_use]
	pub fn reverse_bits(self) -> Self {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		//	Reverse each byte's bits and place in opposite position
		for i in 0..Self::BYTES as usize {
			let mut byte = self.0[i];
			
			//	Reverse the bits in this byte
			byte = ((byte & 0xF0) >> 4_i32) | ((byte & 0x0F) << 4_i32);
			byte = ((byte & 0xCC) >> 2_i32) | ((byte & 0x33) << 2_i32);
			byte = ((byte & 0xAA) >> 1_i32) | ((byte & 0x55) << 1_i32);
			
			//	Place in opposite position
			result[Self::BYTES as usize - 1 - i] = byte;
		}
		
		//	For non-byte-aligned types we need to shift everything right by 1 to
		//	account for the missing bit
		let extra_bits = 8 - (Self::BITS % 8);
		//	Skip if we're byte-aligned
		if extra_bits != 8 {
			let mut carry = 0_u8;
			for i in (0..Self::BYTES as usize).rev() {
				let new_carry = result[i] << (8 - extra_bits);
				result[i]     = carry | (result[i] >> extra_bits);
				carry         = new_carry;
			}
		}
		
		//	Ensure padding bits are cleared
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
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
	pub fn rotate_left(self, n: u32) -> Self {
		//	Normalize rotation amount
		let shift = n % u32::from(Self::BITS);
		if shift == 0 {
			return self;
		}
		
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		//	Calculate main shifts
		#[expect(clippy::integer_division, reason = "Precision is not needed here")]
		let byte_shift = (shift / 8) as usize;
		let bit_shift  = (shift % 8) as u8;
		
		if bit_shift == 0 {
			//	Byte-aligned rotation
			for i in 0..Self::BYTES as usize {
				let src   = (i + Self::BYTES as usize - byte_shift) % Self::BYTES as usize;
				result[i] = self.0[src];
			}
		} else {
			//	Complex case - bits cross byte boundaries
			for i in 0..Self::BYTES as usize {
				//	Get bits from current byte shifted left
				let mut byte = self.0[i] << bit_shift;
				
				//	Get bits from previous byte
				let prev_idx = (i + Self::BYTES as usize - 1) % Self::BYTES as usize;
				byte        |= self.0[prev_idx] >> (8 - bit_shift);
				
				let dest     = (i + byte_shift) % Self::BYTES as usize;
				result[dest] = byte;
			}
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
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
	pub fn rotate_right(self, n: u32) -> Self {
		//	Normalize rotation amount
		let shift = n % u32::from(Self::BITS);
		if shift == 0 {
			return self;
		}
		
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		//	Calculate main shifts
		#[expect(clippy::integer_division, reason = "Precision is not needed here")]
		let byte_shift = (shift / 8) as usize;
		let bit_shift  = (shift % 8) as u8;
		
		if bit_shift == 0 {
			//	Byte-aligned rotation
			for i in 0..Self::BYTES as usize {
				let src   = (i + byte_shift) % Self::BYTES as usize;
				result[i] = self.0[src];
			}
		} else {
			//	Complex case - bits cross byte boundaries
			for i in 0..Self::BYTES as usize {
				//	Get bits from current byte shifted right
				let mut byte = self.0[i] >> bit_shift;
				
				//	Get bits from next byte
				let next_idx = (i + 1) % Self::BYTES as usize;
				byte        |= self.0[next_idx] << (8 - bit_shift);
				
				let dest     = (i + Self::BYTES as usize - byte_shift) % Self::BYTES as usize;
				result[dest] = byte;
			}
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
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
		let (result, overflow) = self.overflowing_add(rhs);
		if overflow {
			if SIGNED {
				//	Return MAX for positive overflow, MIN for negative overflow
				let a_sign = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
				let b_sign = ( rhs.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
				if a_sign == b_sign && a_sign == 0 {
					Self::max_value()
				} else {
					Self::min_value()
				}
			} else {
				Self::max_value()
			}
		} else {
			result
		}
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
	#[must_use]
	pub fn saturating_div(self, rhs: Self) -> Self {
		if rhs.is_zero() {
			return Self::max_value();
		}
		
		//	For signed numbers, check MIN/-1 case
		if SIGNED && self == Self::min_value() && rhs == -Self::one() {
			//	Saturate instead of overflowing
			return Self::max_value();
		}
		
		self.checked_div(rhs).unwrap_or_else(|| {
			if SIGNED {
				if self.is_negative() == rhs.is_negative() {
					Self::max_value()
				} else {
					Self::min_value()
				}
			} else {
				Self::max_value()
			}
		})
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
		let (result, overflow) = self.overflowing_mul(rhs);
		if overflow {
			if SIGNED {
				//	Return MAX for positive overflow, MIN for negative overflow
				let a_sign = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
				let b_sign = ( rhs.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
				if a_sign == b_sign {
					Self::max_value()
				} else {
					Self::min_value()
				}
			} else {
				Self::max_value()
			}
		} else {
			result
		}
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
		self.checked_pow(rhs).map_or_else(|| if SIGNED {
			//	For negative base, depends on whether exponent is even/odd
			let is_negative = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1 == 1;
			if is_negative && rhs % 2 == 1 {
				Self::min_value()
			} else {
				Self::max_value()
			}
		} else {
			Self::max_value()
		}, |result| result)
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
	pub fn saturating_sub(self, rhs: Self) -> Self {
		let (result, overflow) = self.overflowing_sub(rhs);
		if overflow {
			if SIGNED {
				//	Return MAX for positive overflow, MIN for negative overflow
				let a_sign = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
				let b_sign = ( rhs.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
				if a_sign == 0 && b_sign == 1 {
					Self::max_value()
				} else {
					Self::min_value()
				}
			} else {
				Self::min_value()
			}
		} else {
			result
		}
	}
	
	//		set_bit																
	/// Sets the value of a specific bit.
	/// 
	/// Returns `false` if the position is out of range. Otherwise, returns
	/// `true` to indicate success. Note that success does not mean the bit was
	/// actually changed.
	/// 
	/// # Parameters
	/// 
	/// * `pos`   - The position of the bit to get, where `0` is the
	///             least-significant bit.
	/// * `value` - The value to set the bit to.
	/// 
	#[expect(clippy::integer_division, reason = "Precision is not needed here")]
	pub fn set_bit(&mut self, pos: u16, value: bool) -> bool {
		if pos >= Self::BITS {
			return false;
		}
		if value {
			self.0[(pos / 8) as usize] |=   1 << (pos % 8);
		} else {
			self.0[(pos / 8) as usize] &= !(1 << (pos % 8));
		}
		true
	}
	
	//		to_be_bytes()														
	/// Returns the bytes in big-endian order.
	/// 
	/// As this type uses little-endian storage internally, this reverses the
	/// bytes before returning.
	/// 
	#[must_use]
	pub fn to_be_bytes(&self) -> GenericArray<u8, BytesForBits<BITS>> {
		let mut value = GenericArray::<u8, BytesForBits<BITS>>::default();
		for i in 0..Self::BYTES as usize {
			value[i] = self.0[Self::BYTES as usize - 1 - i];
		}
		value
	}
	
	//		to_json																
	/// Serialises this integer to a JSON string.
	/// 
	/// # Errors
	/// 
	/// If the number cannot be serialised for whatever reason, an error will be
	/// returned. In reality this should be infallible.
	/// 
	pub fn to_json(&self) -> Result<String, JsonError> {
		serde_json::to_string(self)
	}
	
	//		to_le_bytes()														
	/// Returns the bytes in little-endian order.
    /// 
    /// As this type uses little-endian storage internally, this is a direct
    /// copy of the internal representation.
	/// 
	#[must_use]
	pub const fn to_le_bytes(&self) -> GenericArray<u8, BytesForBits<BITS>> {
		self.0
	}
	
	//		to_vec()														
	/// Represents the internal value as a [`Vec`] of bytes.
	#[must_use]
	pub fn to_vec(&self) -> Vec<u8> {
		self.0.to_vec()
	}
	
	//		trailing_ones														
	/// Counts the number of trailing ones in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is zero.
	/// 
	#[must_use]
	pub fn trailing_ones(self) -> u16 {
		//	Start with first byte
		#[expect(clippy::cast_possible_truncation, reason = "trailing_ones() returns at most 8 for u8 input")]
		let mut count = self.0[0].trailing_ones() as u16;
		
		//	If we found any non-ones, we're done
		if count < 8 {
			return count;
		}
		
		//	Count through remaining bytes
		for i in 1..Self::BYTES as usize {
			#[expect(clippy::cast_possible_truncation, reason = "trailing_ones() returns at most 8 for u8 input")]
			let ones = self.0[i].trailing_ones() as u16;
			count   += ones;
			if ones < 8 {
				break;
			}
		}
		
		//	Cap at total bits
		count.min(Self::BITS)
	}
	
	//		trailing_zeros														
	/// Counts the number of trailing zeroes in the binary representation of the
	/// value.
	/// 
	/// If the value is zero, the result is the number of bits in the value.
	/// 
	#[must_use]
	pub fn trailing_zeros(self) -> u16 {
		//	Start with first byte
		#[expect(clippy::cast_possible_truncation, reason = "trailing_ones() returns at most 8 for u8 input")]
		let mut count = self.0[0].trailing_zeros() as u16;
		
		//	If we found any non-zeros, we're done
		if count < 8 {
			return count;
		}
		
		//	Count through remaining bytes
		for i in 1..Self::BYTES as usize {
			#[expect(clippy::cast_possible_truncation, reason = "trailing_ones() returns at most 8 for u8 input")]
			let zeros = self.0[i].trailing_zeros() as u16;
			count    += zeros;
			if zeros < 8 {
				break;
			}
		}
		
		//	Cap at total bits
		count.min(Self::BITS)
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
	pub fn wrapping_add(self, rhs: Self) -> Self {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		let mut carry  = 0_u8;
		
		//	Add bytes with carry
		for i in 0..Self::BYTES as usize {
			let (sum1, c1) = self.0[i].overflowing_add(rhs.0[i]);
			let (sum2, c2) = sum1.overflowing_add(carry);
			result[i]      = sum2;
			carry          = u8::from(c1 || c2);
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
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
	#[must_use]
	pub fn wrapping_div(self, rhs: Self) -> Self {
		self.checked_div(rhs).unwrap_or_else(|| {
			if rhs.is_zero() {
				Self::max_value()
			} else if SIGNED && self == Self::min_value() && rhs == -Self::one() {
				//	MIN/-1 wraps to itself
				self
			} else {
				let mut result = self;
				result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
				result
			}
		})
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
	pub fn wrapping_mul(self, rhs: Self) -> Self {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		//	For each byte of self
		for i in 0..Self::BYTES as usize {
			let mut carry = 0_u16;
			
			//	Multiply this byte by each byte of rhs
			for j in 0..Self::BYTES as usize {
				if i + j >= Self::BYTES as usize {
					break;
				}
				
				//	Multiply bytes and add carry
				#[expect(
					clippy::cast_possible_truncation,
					reason = "Lower 8 bits used for result, upper bits captured in carry"
				)]
				{
					let prod      = (u16::from(self.0[i]) * u16::from(rhs.0[j])) + carry + u16::from(result[i + j]);
					result[i + j] = prod as u8;
					carry         = prod >> 8_i32;
				}
			}
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
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
	pub fn wrapping_pow(self, mut rhs: u32) -> Self {
		if rhs == 0 {
			return Self::one();
		}
		
		let mut base   = self;
		let mut result = Self::one();
		
		while rhs > 0 {
			if rhs & 1 == 1 {
				result = result.wrapping_mul(base);
			}
			rhs >>= 1_i32;
			if rhs > 0 {
				base = base.wrapping_mul(base);
			}
		}
		
		result
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
	#[must_use]
	pub fn wrapping_rem(self, rhs: Self) -> Self {
		self.checked_rem(rhs).unwrap_or_else(|| {
			if rhs.is_zero() {
				Self::max_value()
			} else if SIGNED && self == Self::min_value() && rhs == -Self::one() {
				Self::zero()
			} else {
				let mut result = self;
				result.0[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
				result
			}
		})
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
	pub fn wrapping_sub(self, rhs: Self) -> Self {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		let mut borrow = 0_u8;
		
		//	Subtract bytes with borrow
		for i in 0..Self::BYTES as usize {
			let (diff1, b1) = self.0[i].overflowing_sub(rhs.0[i]);
			let (diff2, b2) = diff1.overflowing_sub(borrow);
			result[i]       = diff2;
			borrow          = u8::from(b1 || b2);
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
	}
	
	//		zero																
	/// The value of `0` as an [`Int`].
	/// 
	/// Ideally this would be a constant, but that's not possible just yet until
	/// Rust stabilises const generic expressions.
	/// 
	#[must_use]
	pub fn zero() -> Self {
		Self(GenericArray::default())
	}
}

//󰭅		Add																		
impl<BITS, const SIGNED: bool> Add for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{

	type Output = Self;
	
	//		add																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn add(self, rhs: Self) -> Self::Output {
		self.checked_add(rhs).expect("Attempt to add overflowed")
	}
}

//󰭅		AddAssign																
impl<BITS, const SIGNED: bool> AddAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		add_assign															
	fn add_assign(&mut self, rhs: Self) {
		*self = *self + rhs;
	}
}

//󰭅		Binary																	
impl<BITS, const SIGNED: bool> Binary for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0b")?;
		}
		
		//	Find first non-zero byte (or last byte if all zero)
		let mut start = Self::BYTES as usize - 1;
		while start > 0 && self.0[start] == 0 {
			start -= 1;
		}
		
		//	Handle first byte without leading zeros
		write!(f, "{:b}", self.0[start] & Self::LAST_BYTE_MASK)?;
		
		//	Handle remaining bytes with full width
		for &byte in self.0[..start].iter().rev() {
			write!(f, "{byte:08b}")?;
		}
		
		Ok(())
	}
}

//󰭅		BitAnd																	
impl<BITS, const SIGNED: bool> BitAnd for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		bitand																
	fn bitand(self, rhs: Self) -> Self::Output {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		for i in 0..Self::BYTES as usize {
			result[i] = self.0[i] & rhs.0[i];
		}
		
		//	No need to mask the result as both inputs are already properly masked
		Self(result)
	}
}

//󰭅		BitAndAssign															
impl<BITS, const SIGNED: bool> BitAndAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		bitand_assign														
	fn bitand_assign(&mut self, rhs: Self) {
		*self = *self & rhs;
	}
}

//󰭅		BitOr																	
impl<BITS, const SIGNED: bool> BitOr for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		bitor																
	fn bitor(self, rhs: Self) -> Self::Output {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		for i in 0..Self::BYTES as usize {
			result[i] = self.0[i] | rhs.0[i];
		}
		
		//	No need to mask the result as both inputs are already properly masked
		Self(result)
	}
}

//󰭅		BitOrAssign																
impl<BITS, const SIGNED: bool> BitOrAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		bitor_assign														
	fn bitor_assign(&mut self, rhs: Self) {
		*self = *self | rhs;
	}
}

//󰭅		BitXor																	
impl<BITS, const SIGNED: bool> BitXor for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		bitxor																
	fn bitxor(self, rhs: Self) -> Self::Output {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		for i in 0..Self::BYTES as usize {
			result[i] = self.0[i] ^ rhs.0[i];
		}
		
		//	No need to mask the result as both inputs are already properly masked
		Self(result)
	}
}

//󰭅		BitXorAssign															
impl<BITS, const SIGNED: bool> BitXorAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		bitxor_assign														
	fn bitxor_assign(&mut self, rhs: Self) {
		*self = *self ^ rhs;
	}
}

//󰭅		Debug																	
impl<BITS, const SIGNED: bool> Debug for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		//	Standard format - Int<bits, signed>(value)
		write!(f, "Int::<{}, {}>({})", Self::BITS, SIGNED, self)?;
		
		//	For alternate formatting (#), show byte array
		if f.alternate() {
			for (i, byte) in self.0.iter().enumerate() {
				if i > 0 {
					write!(f, ", ")?;
				}
				write!(f, "0x{byte:02x}")?;
			}
			write!(f, "])")?;
		}
		
		Ok(())
	}
}

//󰭅		Deserialize																
impl<'de, BITS, const SIGNED: bool> Deserialize<'de> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		if deserializer.is_human_readable() {
			//	If the format is human-readable, accept both numbers and strings
			deserializer.deserialize_any(IntVisitor::<BITS, SIGNED>(PhantomData))
		} else {
			//	For binary formats, expect raw bytes
			deserializer.deserialize_bytes(BytesVisitor::<BITS, SIGNED>(PhantomData))
		}
	}
}

//󰭅		Display																	
impl<BITS, const SIGNED: bool> Display for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		//	Handle zero case
		if self.is_zero() {
			return write!(f, "0");
		}
		
		//	For signed negative numbers, output minus and convert to positive
		if SIGNED && self.is_negative() {
			write!(f, "-")?;
			//	Compute absolute value by inverting and adding 1
			let mut abs   = GenericArray::<u8, BytesForBits<BITS>>::default();
			let mut carry = 1_u8;
			for i in 0..Self::BYTES as usize {
				let (sum, c) = (!self.0[i]).overflowing_add(carry);
				abs[i]       = sum;
				carry        = u8::from(c);
			}
			//	Clear padding bits
			abs[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
			return Display::fmt(&Self(abs), f);
		}
		
		//	Convert to decimal digits
		let mut digits    = Vec::new();
		let mut remaining = *self;
		
		//	For values that can't store 10 (1-3 bits), handle directly
		if Self::BITS < 4 {
			//	For these small sizes, we can only have values 0-7 (3 bits), 0-3
			//	(2 bits), or 0-1 (1 bit). We've already handled zero, so we just convert
			//	the value directly.
			digits.push(match char::from_digit(u32::from(remaining.0[0]), 10) {
				Some(d) => d,
				None    => return Err(fmt::Error),
			});
		} else {
			//	Create 10 - safe now as we know we have enough bits
			let ten = {
				let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
				bytes[0]      = 10;
				Self(bytes)
			};
			
			while !remaining.is_zero() {
				let rem   = remaining.wrapping_rem(ten);
				remaining = remaining.wrapping_div(ten);
				let digit = u32::from(rem.0[0]);
				digits.push(match char::from_digit(digit, 10) {
					Some(d) => d,
					None    => return Err(fmt::Error),
				});
			}
		}
		
		//	Write digits in reverse order
		for digit in digits.iter().rev() {
			write!(f, "{digit}")?;
		}
		
		Ok(())
	}
}

//󰭅		Div																		
impl<BITS, const SIGNED: bool> Div for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		div																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn div(self, rhs: Self) -> Self::Output {
		assert!(!rhs.is_zero(), "Attempt to divide by zero");
		self.checked_div(rhs).expect("Attempt to divide overflowed")
	}
}

//󰭅		DivAssign																
impl<BITS, const SIGNED: bool> DivAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		div_assign															
	fn div_assign(&mut self, rhs: Self) {
		*self = *self / rhs;
	}
}

//󰭅		FromSql																	
impl<'a, BITS, const SIGNED: bool> FromSql<'a> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		from_sql															
	fn from_sql(ty: &Type, raw: &'a [u8]) -> Result<Self, Box<dyn Error + Sync + Send>> {
		match ty {
			&Type::INT2 => Ok(Self::try_from(i16::from_sql(ty, raw)?).map_err(Box::new)?),
			&Type::INT4 => Ok(Self::try_from(i32::from_sql(ty, raw)?).map_err(Box::new)?),
			&Type::INT8 => Ok(Self::try_from(i64::from_sql(ty, raw)?).map_err(Box::new)?),
			&Type::TEXT => Ok(
				String::from_utf8(raw.to_vec()).map_err(Box::new)?.parse::<Self>().map_err(Box::new)?
			),
			unknown     => Err(Box::new(IoError::new(
				IoErrorKind::InvalidData,
				format!("Invalid type for Int<{}, {}>: {}", Self::BITS, SIGNED, unknown),
			))),
		}
	}
	
	//		accepts																
	fn accepts(ty: &Type) -> bool {
		matches!(*ty, Type::INT2 | Type::INT4 | Type::INT8 | Type::TEXT)
	}
}

//󰭅		FromStr																	
impl<BITS, const SIGNED: bool> FromStr for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Err = ConversionError;
	
	//		from_str															
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let trimmed = s.trim();
		
		if trimmed.is_empty() {
			return Err(ConversionError::EmptyValue);
		}
		
		//	Find index after signs, scanning character by character
		let index       = trimmed.chars().position(|c| !matches!(c, '-' | '+')).unwrap_or(trimmed.len());
		//	Count minus signs safely by iterating chars
		let minus_count = trimmed.chars().take(index).filter(|&c| c == '-').count();
		
		//	Handle sign for signed numbers
		let (without_sign, is_negative) = if SIGNED {
			(trimmed, minus_count % 2 == 1)
		} else {
			if minus_count % 2 == 1 {
				return Err(ConversionError::ValueIsNegative);
			}
			(trimmed, false)
		};
		
		//	Handle different bases
		#[expect(clippy::option_if_let_else, reason = "Clearer to read as if-let-else")]
		let (without_base, radix) =
			if        let Some(rest) = without_sign.strip_prefix("0x").or_else(|| without_sign.strip_prefix("0X")) {
				(rest, 16)
			} else if let Some(rest) = without_sign.strip_prefix("0b").or_else(|| without_sign.strip_prefix("0B")) {
				(rest, 2)
			} else if let Some(rest) = without_sign.strip_prefix("0o").or_else(|| without_sign.strip_prefix("0O")) {
				(rest, 8)
			} else {
				(without_sign, 10)
			}
		;
		
		if without_base.is_empty() {
			return Err(ConversionError::EmptyValue);
		}
		
		//	Parse the absolute value
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		let mut value = 0_u64;
		
		for c in without_base.chars() {
			let digit = match c {
				'0'..='9' => c as u8 - b'0',
				'a'..='f' => c as u8 - b'a' + 10,
				'A'..='F' => c as u8 - b'A' + 10,
				'_'       => continue,  //  Allow underscores between digits
				_         => return Err(ConversionError::InvalidDigit(c)),
			};
			
			if digit >= radix {
				return Err(ConversionError::InvalidRadix(c, radix));
			}
			
			//	Check for overflow before multiplying
			#[expect(clippy::integer_division, reason = "Precision is not needed here")]
			if value > (u64::MAX / u64::from(radix)) {
				return Err(ConversionError::ValueTooLarge);
			}
			value *= u64::from(radix);
			
			//	Check for overflow before adding
			if value > u64::MAX - u64::from(digit) {
				return Err(ConversionError::ValueTooLarge);
			}
			value += u64::from(digit);
		}
		
		//	Handle negative numbers for signed types
		if SIGNED && is_negative {
			//	Check if negation would overflow
			if value > (1_u64 << (Self::BITS - 1)) {
				return Err(ConversionError::ValueTooLarge);
			}
			value = (1_u64 << Self::BITS) - value;
		} else if value >= (1_u64 << (if SIGNED { Self::BITS - 1 } else { Self::BITS })) {
			return Err(ConversionError::ValueTooLarge);
		}
		
		//	Convert to bytes
		#[expect(
			clippy::cast_possible_truncation,
			reason = "Value masked by position shift, so only relevant bits remain"
		)]
		result.iter_mut().enumerate()
			.for_each(|(pos, byte)| *byte = (value >> (pos * 8)) as u8)
		;
		
		Ok(Self(result))
	}
}

//󰭅		LowerExp																
impl<BITS, const SIGNED: bool> LowerExp for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	#[expect(clippy::string_slice, reason = "We control the String contents here, all ASCII characters")]
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		//	Handle zero case
		if self.is_zero() {
			return write!(f, "0e0");
		}
		
		//	For negative numbers, handle sign separately
		if SIGNED && self.is_negative() {
			write!(f, "-")?;
			return LowerExp::fmt(&-*self, f);
		}
		
		//	Convert to string first to get all digits
		let s   = self.to_string();
		let len = s.len();
		
		if len == 1 {
			//	Single digit
			write!(f, "{s}e0")
		} else {
			//	Remove trailing zeros
			let digits = s.trim_end_matches('0').len();
			
			//	If everything was zeros after first digit
			if digits == 1 {
				write!(f, "{}e{}", &s[..1], len - 1)
			} else {
				//	Limit precision to 19 digits (like u64)
				write!(f, "{}.{}e{}",
					&s[..1],                //  First digit
					&s[1..digits.min(19)],  //  Remaining digits
					len - 1                 //  Exponent is length minus 1
				)
			}
		}
	}
}

//󰭅		LowerHex																
impl<BITS, const SIGNED: bool> LowerHex for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0x")?;
		}
		
		//	Find first non-zero byte (or last byte if all zero)
		let mut start = Self::BYTES as usize - 1;
		while start > 0 && self.0[start] == 0 {
			start -= 1;
		}
		
		//	Handle first byte without leading zeros
		write!(f, "{:x}", self.0[start] & Self::LAST_BYTE_MASK)?;
		
		//	Handle remaining bytes with full width
		for &byte in self.0[..start].iter().rev() {
			write!(f, "{byte:02x}")?;
		}
		
		Ok(())
	}
}

//󰭅		Mul																		
impl<BITS, const SIGNED: bool> Mul for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		mul																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn mul(self, rhs: Self) -> Self::Output {
		self.checked_mul(rhs).expect("Attempt to multiply overflowed")
	}
}

//󰭅		MulAssign																
impl<BITS, const SIGNED: bool> MulAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		mul_assign															
	fn mul_assign(&mut self, rhs: Self) {
		*self = *self * rhs;
	}
}

//󰭅		Neg																		
impl<BITS, const SIGNED: bool> Neg for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
	Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		neg																	
	fn neg(self) -> Self::Output {
		assert!(SIGNED, "Attempt to negate an unsigned value");
		
		//	Special case: negating minimum value would overflow
		assert!(!(self == Self::min_value()), "Attempt to negate integer with overflow");
		
		//	Compute two's complement by inverting all bits and adding 1
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		//	Add 1 for two's complement
		let mut carry  = 1_u8;
		
		for i in 0..Self::BYTES as usize {
			let (sum, new_carry) = (!self.0[i]).overflowing_add(carry);
			result[i] = sum;
			carry     = u8::from(new_carry);
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
	}
}

//󰭅		Not																		
impl<BITS, const SIGNED: bool> Not for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		not																	
	fn not(self) -> Self::Output {
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		for i in 0..Self::BYTES as usize {
			result[i] = !self.0[i];
		}
		
		//	Must mask the result as NOT will set padding bits
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		Self(result)
	}
}

//󰭅		Octal																	
impl<BITS, const SIGNED: bool> Octal for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0o")?;
		}
		
		//	Handle zero case
		if self.is_zero() {
			return write!(f, "0");
		}
		
		//	For negative numbers in signed types
		if SIGNED && self.is_negative() {
			write!(f, "-")?;
			return Octal::fmt(&-*self, f);
		}
		
		//	Convert to octal digits
		let mut digits    = Vec::new();
		let mut remaining = *self;
		//	Create 8 - safe now as we know we have enough bits
		let eight = {
			let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
			bytes[0]      = 8;
			Self(bytes)
		};
		
		while !remaining.is_zero() {
			let rem   = remaining.wrapping_rem(eight);
			remaining = remaining.wrapping_div(eight);
			let digit = u32::from(rem.0[0]);
			digits.push(match char::from_digit(digit, 8) {
				Some(d) => d,
				None    => return Err(fmt::Error),
			});
		}
		
		//	Write digits in reverse order
		for &digit in digits.iter().rev() {
			write!(f, "{digit}")?;
		}
		
		Ok(())
	}
}

//󰭅		Product																	
impl<BITS, const SIGNED: bool> Product for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		product																
	fn product<I>(iter: I) -> Self
	where
		I: Iterator<Item = Self>,
	{
		iter.fold(Self::one(), |acc, x| acc * x)
	}
}

//󰭅		Product<&>																
impl<'a, BITS, const SIGNED: bool> Product<&'a Self> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		product																
	fn product<I>(iter: I) -> Self
	where
		I: Iterator<Item = &'a Self>,
	{
		iter.fold(Self::one(), |acc, &x| acc * x)
	}
}

//󰭅		Rem																		
impl<BITS, const SIGNED: bool> Rem for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		rem																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn rem(self, rhs: Self) -> Self::Output {
		assert!(!rhs.is_zero(), "Attempt to calculate remainder with a divisor of zero");
		self.checked_rem(rhs).expect("Attempt to calculate remainder overflowed")
	}
}

//󰭅		RemAssign																
impl<BITS, const SIGNED: bool> RemAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		rem_assign															
	fn rem_assign(&mut self, rhs: Self) {
		*self = *self % rhs;
	}
}

//󰭅		Serialize																
impl<BITS, const SIGNED: bool> Serialize for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		serialize															
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		if serializer.is_human_readable() {
			//	For JSON and similar formats, serialise as number if it fits in i64/u64
			if Self::BITS <= 64 {
				if SIGNED {
					if let Ok(v) = i64::try_from(*self) {
						return serializer.serialize_i64(v);
					}
				} else if let Ok(v) = u64::try_from(*self) {
					return serializer.serialize_u64(v);
				}
			}
			//	Fall back to string for larger numbers
			serializer.serialize_str(&self.to_string())
		} else {
			//	For binary formats, serialise raw bytes
			serializer.serialize_bytes(&self.0)
		}
	}
}

//󰭅		Shl																		
impl<BITS, const SIGNED: bool> Shl<u32> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		shl																	
	fn shl(self, rhs: u32) -> Self::Output {
		//	Shifts of exactly BITS return 0
		if rhs == u32::from(Self::BITS) {
			return Self::zero();
		}
		
		//	For shifts > BITS, subtract BITS+1
		let effective_shift = if rhs > u32::from(Self::BITS) {
			rhs - (u32::from(Self::BITS) + 1)
		} else {
			rhs
		};
		
		if effective_shift == 0 {
			return self;
		}
		
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		//	Calculate byte and bit offsets
		#[expect(clippy::integer_division, reason = "Precision is not needed here")]
		let byte_shift = (effective_shift / 8) as usize;
		let bit_shift  = (effective_shift % 8) as u8;
		
		if bit_shift == 0 {
			//	Simple case - byte aligned shift
			for i in byte_shift..Self::BYTES as usize {
				if i - byte_shift < Self::BYTES as usize {
					result[i] = self.0[i - byte_shift];
				}
			}
		} else {
			//	Complex case - bits cross byte boundaries
			for i in byte_shift..Self::BYTES as usize {
				//	Get the main bits from the current byte
				let mut byte = if i - byte_shift < Self::BYTES as usize {
					self.0[i - byte_shift] << bit_shift
				} else {
					0
				};
				
				//	Get the remaining bits from the previous byte
				if i > byte_shift && i - byte_shift - 1 < Self::BYTES as usize {
					byte |= self.0[i - byte_shift - 1] >> (8 - bit_shift);
				}
				
				result[i] = byte;
			}
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
	}
}

//󰭅		ShlAssign																
impl<BITS, const SIGNED: bool> ShlAssign<u32> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		shl_assign															
	fn shl_assign(&mut self, rhs: u32) {
		*self = *self << rhs;
	}
}

//󰭅		Shr																		
impl<BITS, const SIGNED: bool> Shr<u32> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		shr																	
	fn shr(self, rhs: u32) -> Self::Output {
		//	Shifts of exactly BITS return 0
		if rhs == u32::from(Self::BITS) {
			return Self::zero();
		}
		
		//	For shifts > BITS, subtract BITS+1
		let effective_shift = if rhs > u32::from(Self::BITS) {
			rhs - (u32::from(Self::BITS) + 1)
		} else {
			rhs
		};
		
		if effective_shift == 0 {
			return self;
		}
		
		let mut result = GenericArray::<u8, BytesForBits<BITS>>::default();
		
		//	Calculate byte and bit offsets
		#[expect(clippy::integer_division, reason = "Precision is not needed here")]
		let byte_shift = (effective_shift / 8) as usize;
		let bit_shift  = (effective_shift % 8) as u8;
		
		if bit_shift == 0 {
			//	Simple case - byte aligned shift
			for i in 0..Self::BYTES as usize - byte_shift {
				result[i] = self.0[i + byte_shift];
			}
		} else {
			//	Complex case - bits cross byte boundaries
			for i in 0..Self::BYTES as usize - byte_shift {
				//	Get the main bits from the current byte
				let mut byte = self.0[i + byte_shift] >> bit_shift;
				
				//	Get the remaining bits from the next byte
				if i + byte_shift + 1 < Self::BYTES as usize {
					byte |= self.0[i + byte_shift + 1] << (8 - bit_shift);
				}
				
				result[i] = byte;
			}
		}
		
		//	For signed numbers, fill with sign bit
		if SIGNED {
			let sign = (self.0[Self::BYTES as usize - 1] >> Self::SIGN_BIT_POS) & 1;
			if sign == 1 {
				//	Fill remaining bytes with 1s
				for i in (Self::BYTES as usize - byte_shift)..Self::BYTES as usize {
					result[i] = 0xFF;
				}
				//	Handle partial byte at boundary if needed
				if bit_shift > 0 && Self::BYTES as usize > byte_shift {
					result[Self::BYTES as usize - byte_shift - 1] |= 0xFF << (8 - bit_shift);
				}
			}
		}
		
		//	Clear any padding bits in last byte
		result[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		
		Self(result)
	}
}

//󰭅		ShrAssign																
impl<BITS, const SIGNED: bool> ShrAssign<u32> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		shr_assign															
	fn shr_assign(&mut self, rhs: u32) {
		*self = *self >> rhs;
	}
}

//󰭅		Sub																		
impl<BITS, const SIGNED: bool> Sub for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Output = Self;
	
	//		sub																	
	#[expect(clippy::expect_used, reason = "Needs to emulate Rust standard library behaviour")]
	fn sub(self, rhs: Self) -> Self::Output {
		self.checked_sub(rhs).expect("Attempt to subtract overflowed")
	}
}

//󰭅		SubAssign																
impl<BITS, const SIGNED: bool> SubAssign for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		sub_assign															
	fn sub_assign(&mut self, rhs: Self) {
		*self = *self - rhs;
	}
}

//󰭅		Sum																		
impl<BITS, const SIGNED: bool> Sum for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		sum																	
	fn sum<I>(iter: I) -> Self
	where
		I: Iterator<Item = Self>,
	{
		iter.fold(Self::min_value(), |acc, x| acc + x)
	}
}

//󰭅		Sum<&>																	
impl<'a, BITS, const SIGNED: bool> Sum<&'a Self> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		sum																	
	fn sum<I>(iter: I) -> Self
	where
		I: Iterator<Item = &'a Self>,
	{
		iter.fold(Self::min_value(), |acc, &x| acc + x)
	}
}

//󰭅		ToSql																	
impl<BITS, const SIGNED: bool> ToSql for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		to_sql																
	fn to_sql(&self, ty: &Type, out: &mut BytesMut) -> Result<IsNull, Box<dyn Error + Sync + Send>> {
		match ty {
			&Type::INT2 => i16::try_from(*self)?.to_sql(ty, out),
			&Type::INT4 => i32::try_from(*self)?.to_sql(ty, out),
			&Type::INT8 => i64::try_from(*self)?.to_sql(ty, out),
			&Type::TEXT => self.to_string().to_sql(ty, out),
			unknown     => Err(Box::new(IoError::new(
				IoErrorKind::InvalidData,
				format!("Invalid type for Int<{}, {}>: {}", Self::BITS, SIGNED, unknown),
			))),
		}
	}
	
	
	//		accepts																
	fn accepts(ty: &Type) -> bool {
		matches!(*ty, Type::INT2 | Type::INT4 | Type::INT8 | Type::TEXT)
	}
	
	to_sql_checked!();
}

//󰭅		TryFrom: i8 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<i8> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i8) -> Result<Self, Self::Error> {
		if !SIGNED && v < 0 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		//	If our type has fewer bits than i8, we need to check range
		//	If our type has 8 or more bits, all i8 values fit
		if SIGNED && Self::BITS < 8 {
			let min = -((i8::MAX >> (7 - (Self::BITS - 1))) + 1);
			let max =    i8::MAX >> (7 - (Self::BITS - 1));
			if v < min || v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		if !SIGNED && Self::BITS < 8 {
			let max = u8::MAX >> (8 - Self::BITS);
			#[expect(clippy::cast_sign_loss, reason = "Safe cast as we've already returned an error if negative")]
			if v as u8 > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		#[expect(clippy::cast_sign_loss, reason = "Safe cast as we've already returned an error if negative")]
		{ bytes[0]    = v as u8; }
		if SIGNED && v < 0 {
			//	Sign extend
			bytes.iter_mut().skip(1).for_each(|b| *b = 0xFF);
			bytes[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		}
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: i16 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<i16> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i16) -> Result<Self, Self::Error> {
		if !SIGNED && v < 0 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		//	If our type has fewer bits than i16, we need to check range
		//	If our type has 16 or more bits, all i16 values fit
		if SIGNED && Self::BITS < 16 {
			let min = -((i16::MAX >> (7 - (Self::BITS - 1))) + 1);
			let max =    i16::MAX >> (7 - (Self::BITS - 1));
			if v < min || v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		if !SIGNED && Self::BITS < 16 {
			let max = u16::MAX >> (16 - Self::BITS);
			#[expect(clippy::cast_sign_loss, reason = "Safe cast as we've already returned an error if negative")]
			if v as u16 > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes[..2].copy_from_slice(&v.to_le_bytes());
		if SIGNED && v < 0 {
			//	Sign extend
			bytes.iter_mut().skip(2).for_each(|b| *b = 0xFF);
			bytes[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		}
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: i32 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<i32> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i32) -> Result<Self, Self::Error> {
		if !SIGNED && v < 0_i32 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		//	If our type has fewer bits than i32, we need to check range
		//	If our type has 32 or more bits, all i32 values fit
		if SIGNED && Self::BITS < 32 {
			let min = -((i32::MAX >> (7 - (Self::BITS - 1))) + 1_i32);
			let max =    i32::MAX >> (7 - (Self::BITS - 1));
			if v < min || v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		if !SIGNED && Self::BITS < 32 {
			let max = u32::MAX >> (32 - Self::BITS);
			#[expect(clippy::cast_sign_loss, reason = "Safe cast as we've already returned an error if negative")]
			if v as u32 > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes[..4].copy_from_slice(&v.to_le_bytes());
		if SIGNED && v < 0_i32 {
			//	Sign extend
			bytes.iter_mut().skip(4).for_each(|b| *b = 0xFF);
			bytes[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		}
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: i64 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<i64> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i64) -> Result<Self, Self::Error> {
		if !SIGNED && v < 0 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		//	If our type has fewer bits than i64, we need to check range
		//	If our type has 64 or more bits, all i64 values fit
		if SIGNED && Self::BITS < 64 {
			let min = -((i64::MAX >> (7 - (Self::BITS - 1))) + 1);
			let max =    i64::MAX >> (7 - (Self::BITS - 1));
			if v < min || v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		if !SIGNED && Self::BITS < 64 {
			let max = u64::MAX >> (64 - Self::BITS);
			#[expect(clippy::cast_sign_loss, reason = "Safe cast as we've already returned an error if negative")]
			if v as u64 > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes[..8].copy_from_slice(&v.to_le_bytes());
		if SIGNED && v < 0 {
			//	Sign extend
			bytes.iter_mut().skip(8).for_each(|b| *b = 0xFF);
			bytes[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		}
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: i128 -> Int													
impl<BITS, const SIGNED: bool> TryFrom<i128> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: i128) -> Result<Self, Self::Error> {
		if !SIGNED && v < 0 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		//	If our type has fewer bits than i128, we need to check range
		//	If our type has 128 or more bits, all i128 values fit
		if SIGNED && Self::BITS < 128 {
			let min = -((i128::MAX >> (7 - (Self::BITS - 1))) + 1);
			let max =    i128::MAX >> (7 - (Self::BITS - 1));
			if v < min || v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		if !SIGNED && Self::BITS < 128 {
			let max = u128::MAX >> (128 - Self::BITS);
			#[expect(clippy::cast_sign_loss, reason = "Safe cast as we've already returned an error if negative")]
			if v as u128 > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		let v_bytes = v.to_le_bytes();
		bytes[..Self::BYTES as usize].copy_from_slice(&v_bytes[..Self::BYTES as usize]);
		if SIGNED && v < 0 {
			bytes[Self::BYTES as usize - 1] &= Self::LAST_BYTE_MASK;
		}
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: isize -> Int													
impl<BITS, const SIGNED: bool> TryFrom<isize> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: isize) -> Result<Self, Self::Error> {
		Self::try_from(v as i64)
	}
}

//󰭅		TryFrom: Int -> i8														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for i8
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED {
			//	Check if value fits in i8
			let sign_bit = (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1;
			if sign_bit == 1 {
				//	Negative number
				if v.0[0] > 128_u8 {
					return Err(ConversionError::ValueTooLarge);
				}
				for &byte in v.0.iter().skip(1) {
					if byte != 0xFF {
						return Err(ConversionError::ValueTooLarge);
					}
				}
				#[expect(
					clippy::cast_possible_wrap,
					reason = "Value verified <= 128 before casting, ensuring valid two's complement"
				)]
				Ok(-((!v.0[0] + 1) as Self))
			} else {
				//	Positive number
				if v.0[0] > 127_u8 {
					return Err(ConversionError::ValueTooLarge);
				}
				for &byte in v.0.iter().skip(1) {
					if byte != 0 {
						return Err(ConversionError::ValueTooLarge);
					}
				}
				#[expect(clippy::cast_possible_wrap, reason = "Value verified <= 127 before casting")]
				Ok(v.0[0] as Self)
			}
		} else {
			//	Unsigned to signed
			if v.0[0] > 127_u8 {
				return Err(ConversionError::ValueTooLarge);
			}
			for &byte in v.0.iter().skip(1) {
				if byte != 0 {
					return Err(ConversionError::ValueTooLarge);
				}
			}
			#[expect(clippy::cast_possible_wrap, reason = "Value verified <= 127 before casting")]
			Ok(v.0[0] as Self)
		}
	}
}

//󰭅		TryFrom: Int -> i16														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for i16
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED {
			//	Check if value fits in i16
			let sign_bit  = (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1;
			let mut bytes = [0_u8; 2];
			bytes.copy_from_slice(&v.0[..2]);
			
			if sign_bit == 1 {
				//	Negative number - verify sign extension
				for &byte in v.0.iter().skip(2) {
					if byte != 0xFF {
						return Err(ConversionError::ValueTooLarge);
					}
				}
				//	Fill remaining bytes with sign extension
				bytes[v.0.len()..2].fill(0xFF);
			} else {
				//	Positive number - verify no overflow
				for &byte in v.0.iter().skip(2) {
					if byte != 0 {
						return Err(ConversionError::ValueTooLarge);
					}
				}
			}
			Ok(Self::from_le_bytes(bytes))
		} else {
			//	For smaller integers, just convert directly
			if v.0.len() <= 2 {
				let mut bytes = [0_u8; 2];
				bytes[..v.0.len()].copy_from_slice(&v.0);
				if bytes[1] > 0x7F {
					return Err(ConversionError::ValueTooLarge);
				}
				return Ok(Self::from_le_bytes(bytes));
			}
			
			//	For larger integers, check for overflow
			if v.0[1] > 0x7F || v.0.iter().skip(2).any(|&b| b != 0) {
				return Err(ConversionError::ValueTooLarge);
			}
			let mut bytes = [0_u8; 2];
			bytes[..2].copy_from_slice(&v.0[..2]);
			Ok(Self::from_le_bytes(bytes))
		}
	}
}

//󰭅		TryFrom: Int -> i32														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for i32
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED {
			//	Check if value fits in i32
			let sign_bit  = (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1;
			let mut bytes = [0_u8; 4];
			bytes.copy_from_slice(&v.0[..4]);
			
			if sign_bit == 1 {
				//	Negative number - verify sign extension
				for &byte in v.0.iter().skip(4) {
					if byte != 0xFF {
						return Err(ConversionError::ValueTooLarge);
					}
				}
				//	Fill remaining bytes with sign extension
				bytes[v.0.len()..4].fill(0xFF);
			} else {
				//	Positive number - verify no overflow
				for &byte in v.0.iter().skip(4) {
					if byte != 0 {
						return Err(ConversionError::ValueTooLarge);
					}
				}
			}
			Ok(Self::from_le_bytes(bytes))
		} else {
			//	For smaller integers, just convert directly
			if v.0.len() <= 4 {
				let mut bytes = [0_u8; 4];
				bytes[..v.0.len()].copy_from_slice(&v.0);
				if bytes[3] > 0x7F {
					return Err(ConversionError::ValueTooLarge);
				}
				return Ok(Self::from_le_bytes(bytes));
			}
			
			//	For larger integers, check for overflow
			if v.0[3] > 0x7F || v.0.iter().skip(4).any(|&b| b != 0) {
				return Err(ConversionError::ValueTooLarge);
			}
			let mut bytes = [0_u8; 4];
			bytes[..4].copy_from_slice(&v.0[..4]);
			Ok(Self::from_le_bytes(bytes))
		}
	}
}

//󰭅		TryFrom: Int -> i64														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for i64
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED {
			//	Check if value fits in i64
			let sign_bit  = (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1;
			let mut bytes = [0_u8; 8];
			bytes.copy_from_slice(&v.0[..8]);
			
			if sign_bit == 1 {
				//	Negative number - verify sign extension
				for &byte in v.0.iter().skip(8) {
					if byte != 0xFF {
						return Err(ConversionError::ValueTooLarge);
					}
				}
				//	Fill remaining bytes with sign extension
				bytes[v.0.len()..8].fill(0xFF);
			} else {
				//	Positive number - verify no overflow
				for &byte in v.0.iter().skip(8) {
					if byte != 0 {
						return Err(ConversionError::ValueTooLarge);
					}
				}
			}
			Ok(Self::from_le_bytes(bytes))
		} else {
			//	For smaller integers, just convert directly
			if v.0.len() <= 8 {
				let mut bytes = [0_u8; 8];
				bytes[..v.0.len()].copy_from_slice(&v.0);
				if bytes[7] > 0x7F {
					return Err(ConversionError::ValueTooLarge);
				}
				return Ok(Self::from_le_bytes(bytes));
			}
			
			//	For larger integers, check for overflow
			if v.0[7] > 0x7F || v.0.iter().skip(8).any(|&b| b != 0) {
				return Err(ConversionError::ValueTooLarge);
			}
			let mut bytes = [0_u8; 8];
			bytes[..8].copy_from_slice(&v.0[..8]);
			Ok(Self::from_le_bytes(bytes))
		}
	}
}

//󰭅		TryFrom: Int -> i128													
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for i128
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED {
			//	Check if value fits in i128
			let sign_bit  = (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1;
			let mut bytes = [0_u8; 16];
			bytes[..v.0.len().min(16)].copy_from_slice(&v.0[..v.0.len().min(16)]);
			
			if sign_bit == 1 {
				//	Negative number - verify sign extension
				for &byte in v.0.iter().skip(16) {
					if byte != 0xFF {
						return Err(ConversionError::ValueTooLarge);
					}
				}
				//	Fill remaining bytes with sign extension
				bytes[v.0.len()..16].fill(0xFF);
			} else {
				//	Positive number - verify no overflow
				for &byte in v.0.iter().skip(16) {
					if byte != 0 {
						return Err(ConversionError::ValueTooLarge);
					}
				}
			}
			Ok(Self::from_le_bytes(bytes))
		} else {
			//	For smaller integers, just convert directly
			if v.0.len() <= 16 {
				let mut bytes = [0_u8; 16];
				bytes[..v.0.len()].copy_from_slice(&v.0);
				if bytes[15] > 0x7F {
					return Err(ConversionError::ValueTooLarge);
				}
				return Ok(Self::from_le_bytes(bytes));
			}
			
			//	For larger integers, check for overflow
			if v.0[15] > 0x7F || v.0.iter().skip(16).any(|&b| b != 0) {
				return Err(ConversionError::ValueTooLarge);
			}
			let mut bytes = [0_u8; 16];
			bytes[..16].copy_from_slice(&v.0[..16]);
			Ok(Self::from_le_bytes(bytes))
		}
	}
}

//󰭅		TryFrom: Int -> isize													
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for isize
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		let value = i64::try_from(v)?;
		if value < Self::MIN as i64 || value > Self::MAX as i64 {
			return Err(ConversionError::ValueTooLarge);
		}
		#[expect(clippy::cast_possible_truncation, reason = "Value verified to be within target platform size")]
		Ok(value as Self)
	}
}

//󰭅		TryFrom: Int -> u8														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for u8
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<Self, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED && (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1 == 1 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		let max = Int::try_from(Self::MAX).unwrap_or_else(|_| Int::max_value());
		if v > max {
			return Err(ConversionError::ValueTooLarge);
		}
		
		for &byte in v.0.iter().skip(1) {
			if byte != 0 {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		Ok(v.0[0])
	}
}

//󰭅		TryFrom: Int -> u16														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for u16
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED && (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1 == 1 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		let mut bytes = [0_u8; 2];
		bytes.copy_from_slice(&v.0[..2]);
		let result = Self::from_le_bytes(bytes);
		
		for &byte in v.0.iter().skip(2) {
			if byte != 0 {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		Ok(result)
	}
}

//󰭅		TryFrom: Int -> u32														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for u32
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED && (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1 == 1 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		let mut bytes = [0_u8; 4];
		bytes.copy_from_slice(&v.0[..4]);
		let result = Self::from_le_bytes(bytes);
		
		for &byte in v.0.iter().skip(4) {
			if byte != 0 {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		Ok(result)
	}
}

//󰭅		TryFrom: Int -> u64														
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for u64
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED && (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1 == 1 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		let mut bytes = [0_u8; 8];
		bytes[..v.0.len().min(8)].copy_from_slice(&v.0[..v.0.len().min(8)]);
		let result = Self::from_le_bytes(bytes);
		
		for &byte in v.0.iter().skip(8) {
			if byte != 0 {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		Ok(result)
	}
}

//󰭅		TryFrom: Int -> u128													
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for u128
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		if SIGNED && (v.0[Int::<BITS, SIGNED>::BYTES as usize - 1] >> Int::<BITS, SIGNED>::SIGN_BIT_POS) & 1 == 1 {
			return Err(ConversionError::ValueIsNegative);
		}
		
		let mut bytes = [0_u8; 16];
		bytes[..v.0.len().min(16)].copy_from_slice(&v.0[..v.0.len().min(16)]);
		let result = Self::from_le_bytes(bytes);
		
		for &byte in v.0.iter().skip(16) {
			if byte != 0 {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		Ok(result)
	}
}

//󰭅		TryFrom: Int -> usize													
impl<BITS, const SIGNED: bool> TryFrom<Int<BITS, SIGNED>> for usize
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: Int<BITS, SIGNED>) -> Result<Self, Self::Error> {
		let value = u64::try_from(v)?;
		if value > Self::MAX as u64 {
			return Err(ConversionError::ValueTooLarge);
		}
		#[expect(clippy::cast_possible_truncation, reason = "Value verified to be within target platform size")]
		Ok(value as Self)
	}
}

//󰭅		TryFrom: u8 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<u8> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u8) -> Result<Self, Self::Error> {
		//	If our type has fewer bits than u8, we need to check range
		//	If our type has 8 or more bits, all u8 values fit
		if Self::BITS < 8 {
			let max = u8::MAX >> (8 - Self::BITS);
			if v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes[0]      = v;
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: u16 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<u16> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u16) -> Result<Self, Self::Error> {
		//	If our type has fewer bits than u16, we need to check range
		//	If our type has 16 or more bits, all u16 values fit
		if Self::BITS < 16 {
			let max = u16::MAX >> (16 - Self::BITS);
			if v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes[..2].copy_from_slice(&v.to_le_bytes());
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: u32 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<u32> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u32) -> Result<Self, Self::Error> {
		//	If our type has fewer bits than u32, we need to check range
		//	If our type has 32 or more bits, all u32 values fit
		if Self::BITS < 32 {
			let max = u32::MAX >> (32 - Self::BITS);
			if v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes[..4].copy_from_slice(&v.to_le_bytes());
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: u64 -> Int														
impl<BITS, const SIGNED: bool> TryFrom<u64> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u64) -> Result<Self, Self::Error> {
		//	If our type has fewer bits than u64, we need to check range
		//	If our type has 64 or more bits, all u64 values fit
		if Self::BITS < 64 {
			let max = u64::MAX >> (64 - Self::BITS);
			if v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes[..8].copy_from_slice(&v.to_le_bytes());
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: u128 -> Int													
impl<BITS, const SIGNED: bool> TryFrom<u128> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: u128) -> Result<Self, Self::Error> {
		//	If our type has fewer bits than u128, we need to check range
		//	If our type has 128 or more bits, all u128 values fit
		if Self::BITS < 128 {
			let max = u128::MAX >> (128 - Self::BITS);
			if v > max {
				return Err(ConversionError::ValueTooLarge);
			}
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		let v_bytes = v.to_le_bytes();
		bytes[..Self::BYTES as usize].copy_from_slice(&v_bytes[..Self::BYTES as usize]);
		Ok(Self(bytes))
	}
}

//󰭅		TryFrom: usize -> Int													
impl<BITS, const SIGNED: bool> TryFrom<usize> for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Error = ConversionError;
	
	//		try_from															
	fn try_from(v: usize) -> Result<Self, Self::Error> {
		Self::try_from(v as u64)
	}
}

//󰭅		UpperExp																
impl<BITS, const SIGNED: bool> UpperExp for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.write_str(&format!("{self:e}").replace('e', "E"))
	}
}

//󰭅		UpperHex																
impl<BITS, const SIGNED: bool> UpperHex for Int<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
		Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	//		fmt																	
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		if f.alternate() {
			write!(f, "0x")?;
		}
		
		//	Find first non-zero byte (or last byte if all zero)
		let mut start = Self::BYTES as usize - 1;
		while start > 0 && self.0[start] == 0 {
			start -= 1;
		}
		
		//	Handle first byte without leading zeros
		write!(f, "{:X}", self.0[start] & Self::LAST_BYTE_MASK)?;
		
		//	Handle remaining bytes with full width
		for &byte in self.0[..start].iter().rev() {
			write!(f, "{byte:02X}")?;
		}
		
		Ok(())
	}
}

//		BytesVisitor															
/// A visitor for parsing integers from bytes.
struct BytesVisitor<BITS, const SIGNED: bool>(PhantomData<BITS>);

//󰭅		Visitor																	
impl<BITS, const SIGNED: bool> Visitor<'_> for BytesVisitor<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
	Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Value = Int<BITS, SIGNED>;
	
	//		expecting															
	fn expecting(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
		write!(formatter, "bytes representing a {} integer", if SIGNED { "signed" } else { "unsigned" })
	}
	
	//		visit_bytes															
	fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
	where
		E: SerdeError,
	{
		if v.len() != Int::<BITS, SIGNED>::BYTES as usize {
			return Err(SerdeError::invalid_length(v.len(), &self));
		}
		
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes.copy_from_slice(v);
		Int::new(bytes).map_err(SerdeError::custom)
	}
}

//		IntVisitor																
/// A visitor for parsing integers from strings.
struct IntVisitor<BITS, const SIGNED: bool>(PhantomData<BITS>);

//󰭅		Visitor																	
impl<BITS, const SIGNED: bool> Visitor<'_> for IntVisitor<BITS, SIGNED>
where
	BITS: Unsigned + Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>> + PartialEq + PartialOrd,
	<BITS as Add<TnUInt<TnUInt<TnUInt<UTerm, B1>, B1>, B1>>>::Output:
	Div<TnUInt<TnUInt<TnUInt<TnUInt<UTerm, B1>, B0>, B0>, B0>>,
	BytesForBits<BITS>: ArrayLength,
	GenericArray<u8, BytesForBits<BITS>>: Copy,
{
	type Value = Int<BITS, SIGNED>;
	
	//		expecting															
	fn expecting(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
		write!(formatter, "an integer")
	}
	
	//		visit_i64															
	fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
	where
		E: SerdeError,
	{
		Int::try_from(v).map_err(E::custom)
	}
	
	//		visit_u64															
	fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
	where
		E: SerdeError,
	{
		Int::try_from(v).map_err(E::custom)
	}
	
	//		visit_str															
	fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
	where
		E: SerdeError,
	{
		v.parse().map_err(E::custom)
	}
	
	//		visit_bytes															
	fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
	where
		E: SerdeError,
	{
		if v.len() != Int::<BITS, SIGNED>::BYTES as usize {
			return Err(E::invalid_length(v.len(), &self));
		}
		let mut bytes = GenericArray::<u8, BytesForBits<BITS>>::default();
		bytes.copy_from_slice(v);
		Int::new(bytes).map_err(E::custom)
	}
}


