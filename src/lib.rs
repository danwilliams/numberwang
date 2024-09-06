//! The Shortints crate is a library of integers that are 1 bit shorter than
//! the standard integer types.



//		Global configuration

//	Customisations of the standard linting configuration
#![allow(clippy::items_after_test_module, reason = "Not needed with separated tests")]

//	Lints specifically disabled for unit tests
#![cfg_attr(test, allow(
	non_snake_case,
	clippy::cast_lossless,
	clippy::cast_precision_loss,
	clippy::cognitive_complexity,
	clippy::default_numeric_fallback,
	clippy::exhaustive_enums,
	clippy::exhaustive_structs,
	clippy::expect_used,
	clippy::indexing_slicing,
	clippy::let_underscore_must_use,
	clippy::let_underscore_untyped,
	clippy::missing_assert_message,
	clippy::missing_panics_doc,
	clippy::must_use_candidate,
	clippy::panic,
	clippy::print_stdout,
	clippy::unwrap_in_result,
	clippy::unwrap_used,
	reason = "Not useful in unit tests"
))]



//		Modules

mod errors;

#[path = "u63.rs"]
mod u63_mod;



//		Packages

pub use errors::ConversionError;
pub use u63_mod::u63;


