//! Contains error types used throughout the library.



//		Packages

use core::num::{ParseIntError, TryFromIntError};
use thiserror::Error as ThisError;



//		Enums

//		ConversionError															
/// Represents all possible conversion errors that can occur.
#[derive(Clone, Debug, Eq, PartialEq, ThisError)]
#[non_exhaustive]
pub enum ConversionError {
	/// The incoming value is empty, e.g. an empty string.
	#[error("Empty value")]
	EmptyValue,
	
	/// The incoming value is not a valid integer.
	#[error("Invalid digit: {0}")]
	InvalidDigit(char),
	
	/// The incoming value is not a valid integer.
	#[error("Invalid digit for base {1}: {0}")]
	InvalidRadix(char, u8),
	
	/// The incoming value is not a valid integer.
	#[error("Invalid integer: {0}")]
	ParseIntError(#[from] ParseIntError),
	
	/// The incoming value is not a valid integer for the destination type.
	#[error("Invalid integer for destination type: {0}")]
	TryFromIntError(#[from] TryFromIntError),
	
	/// The incoming value is negative, which is not allowed by the destination
	/// type.
	#[error("Value is negative")]
	ValueIsNegative,
	
	/// The incoming value is too large to be converted to the destination type.
	#[error("Value too large")]
	ValueTooLarge,
}


