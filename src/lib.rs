//! The Numberwang crate is a library of custom number types and functionality.



//		Global configuration

//	Customisations of the standard linting configuration
#![allow(clippy::items_after_test_module, reason = "Not needed with separated tests")]
#![allow(clippy::multiple_crate_versions, reason = "generic_array deep dependency waiting for digest update")]

//	Lints specifically disabled for unit tests
#![cfg_attr(test, allow(
	non_snake_case,
	clippy::arithmetic_side_effects,
	clippy::cast_lossless,
	clippy::cast_precision_loss,
	clippy::cognitive_complexity,
	clippy::default_numeric_fallback,
	clippy::exhaustive_enums,
	clippy::exhaustive_structs,
	clippy::expect_used,
	clippy::indexing_slicing,
	clippy::integer_division,
	clippy::let_underscore_must_use,
	clippy::let_underscore_untyped,
	clippy::missing_assert_message,
	clippy::missing_panics_doc,
	clippy::must_use_candidate,
	clippy::panic,
	clippy::print_stdout,
	clippy::too_many_lines,
	clippy::unwrap_in_result,
	clippy::unwrap_used,
	reason = "Not useful in unit tests"
))]



//		Modules

mod errors;
mod int;



//		Packages

pub use errors::ConversionError;
pub use int::{BytesForBits, Int, SInt, UInt};


