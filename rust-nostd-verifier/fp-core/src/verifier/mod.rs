//! The verifier's shared core, its transcript adapter, its public tables and digest gate, and the
//! sub-proof engine with its smallness test, lookup argument and sumchecks.

pub mod attention_check;
pub mod attention_plan;
pub mod attention_run;
pub mod attention_shape;
pub mod common;
pub mod engine;
pub mod lookup;
pub mod matrices;
pub mod packing;
pub mod segment;
pub mod smallness;
pub mod sumcheck;
pub mod tables;
pub mod transcript;
