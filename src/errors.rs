//! Contains error types used throughout the library.



//		Packages

use thiserror::Error as ThisError;



//		Enums

//		ConversionError															
/// Represents all possible conversion errors that can occur.
#[derive(Clone, Debug, Eq, PartialEq, ThisError)]
#[non_exhaustive]
pub enum ConversionError {
	/// The incoming value is negative, which is not allowed by the destination
	/// type.
	#[error("Value is negative")]
	ValueIsNegative,
	
	/// The incoming value is too large to be converted to the destination type.
	#[error("Value too large")]
	ValueTooLarge,
}


