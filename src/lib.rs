//! The Shortints crate is a library of integers that are 1 bit shorter than
//! the standard integer types.



//		Global configuration

#![cfg_attr(feature = "reasons", feature(lint_reasons))]

//	Customisations of the standard linting configuration
#![cfg_attr(    feature = "reasons",  allow(clippy::items_after_test_module, reason = "Not needed with separated tests"))]
#![cfg_attr(not(feature = "reasons"), allow(clippy::items_after_test_module))]

//	Lints specifically disabled for unit tests
#![cfg_attr(test, allow(
	clippy::cognitive_complexity,
	clippy::exhaustive_enums,
	clippy::exhaustive_structs,
	clippy::expect_used,
	clippy::indexing_slicing,
	clippy::let_underscore_untyped,
	clippy::missing_assert_message,
	clippy::missing_panics_doc,
	clippy::must_use_candidate,
	clippy::panic,
	clippy::print_stdout,
	clippy::unwrap_in_result,
	clippy::unwrap_used,
))]



//		Modules

#[path = "u63.rs"]
mod u63_mod;



//		Packages

pub use u63_mod::u63;


