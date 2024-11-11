# Numberwang

![Rust](https://img.shields.io/badge/Rust-1.81%2B-b7410e?style=flat&logo=rust&logoColor=white&labelColor=b7410e)
[![Crate version](https://img.shields.io/crates/v/numberwang?style=flat)](https://crates.io/crates/numberwang)
[![CI](https://img.shields.io/github/actions/workflow/status/danwilliams/numberwang/ci.yml?style=flat&logo=github&logoColor=white&label=build%2Ftest)](https://github.com/danwilliams/numberwang/actions/workflows/ci.yml)
[![Docs](https://img.shields.io/docsrs/numberwang?style=flat&logo=docs.rs&logoColor=white)](https://docs.rs/crate/numberwang/latest)
![License](https://img.shields.io/github/license/danwilliams/numberwang?style=flat)

The Numberwang crate is a library of custom number types and functionality,
including variable-bit-width integers.

It is named after the fictitious game show "Numberwang", which is a running joke
in the British sketch comedy show *That Mitchell and Webb Look*. The name was
chosen because the crate is all about numbers.

The modules provided are:

  - [int](#int)


# int

The [`int`](https://docs.rs/numberwang/latest/numberwang/int/index.html) module
provides a variable-bit-width integer type, [`Int`](https://docs.rs/numberwang/latest/numberwang/int/struct.Int.html),
which can be used to store integers of any bit width, from 1 to 65,536 bits.

This is particularly useful for situations such as:

  - **Database compatibility:** This type can be used to create an unsigned
    63-bit integer to represent the crossover between a [`u64`] (which would be
    the choice for the types used in Rust) and an [`i64`] (which is a limitation
    of certain databases, e.g. PostgreSQL). This is necessary in order to safely
    represent the values in the database without losing any information.

  - **Efficiency:** This type is also useful for efficiency, as it can be used
    to create integers that only take the space they need between the standard
    sizes, e.g. 24-bit, 48-bit, etc.

  - **Higher boundaries:** This type can also be used to create integers with
    higher boundaries than the standard Rust integer types, e.g. 256-bit,
    512-bit, etc. all the way up to 65,536-bit.

The type implements all standard Rust functionality for integers, and follows
standard Rust conventions, meaning it should be intuitive to use. It also
correctly observes Endian rules and interoperability, in terms of both bits and
bytes.


