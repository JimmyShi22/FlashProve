# S5 report: SP1 guest execution and cycle measurements

S5 runs the S3 verifier inside an SP1 guest and measures what one execution costs. The guest reuses
`fp-core` read-only: the three stages run through `fp_core::verifier::run_stage`, and a small
assembly in the guest produces the same `result-v1` line and `YES` that `fp-host` prints. The host
calls SP1's execute API only (no proving) and compares the guest's public output with `fp-host`
line by line.

## 1. Toolchain

| Piece | Version | How it was installed |
|---|---|---|
| `cargo prove` (`sp1-cli` package) | **6.10.0** | `cargo install sp1-cli --version 6.10.0 --locked` |
| SP1 zkVM toolchain (`succinct`) | rustc **1.96.0-dev** | `cargo prove install-toolchain` |
| zkVM targets shipped | `riscv64im-succinct-zkvm-elf`, `riscv32im-succinct-zkvm-elf` | in `~/.sp1/toolchains/<id>/lib/rustlib/` |
| Host Rust | rustc 1.97.1 | the repository's toolchain |
| `sp1-zkvm`, `sp1-sdk`, `sp1-core-executor` | pinned `=6.10.0` | `zkvm/guest/Cargo.toml`, `zkvm/host-exec/Cargo.toml` |

`cargo prove --version` prints `cargo-prove sp1 (VERGEN_IDEMPOTENT_OUTPUT 2026-11-05T07:35:46Z)`;
the version is the crates.io package `sp1-cli 6.10.0`, which is the crate that ships the
`cargo-prove` binary (`cargo install cargo-prove` names no crates.io package).

The 6.10.0 toolchain ships both zkVM targets. `cargo prove build` selects
`riscv64im-succinct-zkvm-elf` (`sp1-build`'s `DEFAULT_TARGET`), and the 6.10.0 executor expects that
target; the S5 task book's `riscv32im-succinct-zkvm-elf` is also installed but is not the one this
toolchain builds by default. This report records the target that was actually used.

## 2. The guest and the host

- `zkvm/guest/` (`#![no_std]`): reads the private input with `sp1_zkvm::io::read` (each byte string
  is length-prefixed: `Vec<u8>`), runs the three stages and commits the call's accounting, its
  `result-v1` line and `YES` (or the rejection) as public output.
- `zkvm/host-exec/` (std): reads the fixtures, writes the same input with `SP1Stdin::write`,
  executes the ELF with `ProverClient::builder().cpu().build()` and `.execute(..).run()`, prints
  the execution report, and compares `result-v1` and `YES` with `fp-host`'s.

The private input is the reference call's five paths flattened: `policy.txt`, `layout.txt`,
`KL.bin` (the configuration folder), `key.bin` and the leaf file that the proof names (the ivk
folder), the request, y and proof files, then the leaf number and the commitment ID.

## 3. Results

*(filled by the S5 run: ELF size, cycles, shards, syscalls, memory, consistency output)*

## 4. Pitfalls and countermeasures

*(filled by the S5 run)*
