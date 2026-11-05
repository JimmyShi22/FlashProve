# S5a-1 report: compile-level optimization of the SP1 guest

S5a-1 changes only the guest's compile configuration. No `.rs` business code and no BLAKE2b
implementation was touched; the C++ sources are untouched.

## 1. Method

- The S5 debug-executor run took 4,672 s per execute, too slow to iterate. `host-exec` was rebuilt
  with `--release` (`cargo build --release -p host-exec`, 2m13s); the release executor runs the same
  guest in about 322–542 s depending on machine load. **The executor's build does not change the
  cycle count**: the release executor reproduced S5's 32,385,267,062 exactly.
- Each experiment is one `cargo prove build -p guest --binaries guest` (plus the experiment's
  `--rustflags`), then one `target/release/host-exec` execute. The host prints the total cycles and
  compares `result-v1` and `YES` with `fp-host`; every measured variant passes that gate.
- The ELF's SHA-256 is recorded: an unchanged hash proves the variant's binary is identical, so its
  cycle count cannot differ.

## 2. The initial state

- `zkvm/Cargo.toml` had no `[profile.release]`. Cargo's release defaults therefore applied:
  `opt-level = 3`, `lto = false`, `codegen-units = 16`, `panic = "unwind"`.
- `sp1-build 6.10.0` always passes these rustflags to the guest build:
  `-C passes=lower-atomic`, `-C link-arg=--image-base=2013265920`, `-C panic=abort`,
  `--cfg getrandom_backend="custom"`,
  `-C llvm-args=-misched-prera-direction=bottomup`,
  `-C llvm-args=-misched-postra-direction=bottomup`.
- The target spec (`rustc --print target-spec-json -Z unstable-options --target
  riscv64im-succinct-zkvm-elf`) has `"features": "+m"` and `"panic-strategy": "abort"`.
  So the multiply extension is already enabled and panics already abort.

## 3. Experiments

| Step | Configuration change | Guest ELF (bytes / SHA-256) | Total cycles | Δ vs previous | Δ vs baseline | Consistency |
|---|---|---|---|---|---|---|
| 0 | none (cargo release defaults) | 3,207,568 / `6644c05a…` | 32,385,267,062 | — | — | PASS |
| 2 | `opt-level = 3` explicit | 3,207,568 / `6644c05a…` (identical) | 32,385,267,062 | 0 | 0 | PASS |
| 3 | `+ lto = "fat"`, `codegen-units = 1` | 2,832,504 / `4fc33452…` | 29,959,850,047 | −2,425,417,015 (−7.49%) | −7.49% | PASS |
| 4 | `+ panic = "abort"` | 2,832,504 / `77c1984a…` | 29,959,850,047 | 0 | −7.49% | PASS |
| 5 | target features: none added | unchanged (no rebuild) | 29,959,850,047 | 0 | −7.49% | n/a |
| 6 | `--rustflags="-Cllvm-args=-inline-threshold=1000"` | 12,194,968 / `8b841981…` | 27,176,326,759 | −2,783,523,288 (−9.29%) | −16.09% | PASS |
| final | `lto = "fat"`, `codegen-units = 1`, the LLVM flag (the two no-op lines removed) | 12,194,968 / `ce966b26…` | see §5 | — | — | see §5 |

Execute wall-clock varied with machine load (542.57 s, 381.30 s, 530.08 s, 482.82 s, 323.13 s) while
the cycle counts repeated exactly; wall-clock is not the metric.

## 4. Attribution

- **`lto = "fat"` + `codegen-units = 1` is the first real win: −7.49%.** Before it, `fp-core` was a
  separate codegen unit with no cross-crate inlining. The ELF also shrank from 3.21 MB to 2.83 MB.
- **The LLVM inlining threshold adds another −9.29% (total −16.09%).** Passing
  `-C llvm-args=-inline-threshold=1000` through `cargo prove build --rustflags` makes LLVM inline
  much more aggressively; the ELF grows 4.3× (2.83 MB → 12.19 MB), but the executed instruction
  count falls. This is the experiment that the S5a task book asked for: the cycle count is
  sensitive to the LLVM pass configuration, and the knob is landable through `--rustflags`
  (note the value must be attached: `--rustflags="-Cllvm-args=..."`; a space after `-C` makes rustc
  read an unknown codegen option).
- **`opt-level = 3` is already the default**: the ELF and the cycles are bit-for-bit identical.
- **`panic = "abort"` changes nothing**: `sp1-build` already passes `-C panic=abort`, and the target
  spec sets the abort strategy; the explicit profile line only changed a metadata byte in the ELF
  (the cycles stayed identical), so it was reverted.
- **No target feature can be added.** The target spec declares `features = "+m"` and `+m` is
  already enabled. `rustc --print target-features` lists other RISC-V features (`+a`, `+c`, …), but
  the SP1 target is RV64IM: its core does not include them, so enabling them is outside the
  declared ISA and was not attempted.

The final build command (reproducible):

```sh
cd zkvm
cargo prove build -p guest --binaries guest --rustflags="-Cllvm-args=-inline-threshold=1000"
# zkvm/Cargo.toml: [profile.release] lto = "fat", codegen-units = 1
```

## 5. Acceptance

The final configuration (`[profile.release] lto = "fat"`, `codegen-units = 1`, and
`--rustflags="-Cllvm-args=-inline-threshold=1000"`) executes the accepted example in
**27,176,326,759 cycles**, against the S5 baseline of **32,385,267,062**: **−5,208,940,303 cycles,
−16.09%**. The run ends with `guest exit code 0`, `status 0`, and the consistency gate:
`host-exec: result-v1 IDENTICAL`, `host-exec: YES IDENTICAL`, `host-exec: PASS (result-v1 and YES
are byte-identical to fp-host)`. The final ELF is 12,194,968 bytes, SHA-256 `ce966b26…` (the
final rebuild differs from Step 6's `8b841981…` only in metadata; its cycle count is identical).

No `.rs` file changed: the only working-tree change of S5a-1 is `zkvm/Cargo.toml`. The C++ sources
are untouched.
