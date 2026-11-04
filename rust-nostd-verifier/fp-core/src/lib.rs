//! FlashProve verifier core, ported from `verifier/src`.
//!
//! S1 scope: constants, the refusal model, header checks, rejection names, the output-parsing
//! helpers and the per-stage state container. The proof system arrives in S2.
//!
//! This crate is `#![no_std]` and allocates only through `alloc`.

#![no_std]

extern crate alloc;

pub mod consts;
pub mod field;
pub mod head;
pub mod names;
pub mod out;
pub mod refusal;
pub mod stage_state;
