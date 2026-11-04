# S1 report: Rust workspace skeleton

- Branch: `feat/nostd-verifier`
- S0 inventory: `docs/nostd-inventory.md` (TL review passed; fixes in commit `19fbba81`)
- S1 scope: workspace, `no_std` core, host shell, CLI, file/header validation, three-stage
  skeleton. Proof system and `result-v1` remain S2/S3.
- No C++ source was modified. No third-party crate was added. No toolchain was installed.

## What was added

| Path | Lines | Purpose |
|---|---:|---|
| `rust-nostd-verifier/Cargo.toml` | 6 | workspace, no dependencies |
| `fp-core/Cargo.toml`, `fp-host/Cargo.toml` | 23 | crate manifests |
| `fp-core/src/lib.rs` | 17 | `#![no_std]` + `extern crate alloc` |
| `fp-core/src/refusal.rs` | 51 | `Refusal::{Named, Internal}` and `Result` |
| `fp-core/src/consts.rs` | 67 | DW/version/tags/build digest/exit statuses/stage defaults |
| `fp-core/src/names.rs` | 331 | all 304 rejection names, source + test-coverage notes |
| `fp-core/src/head.rs` | 69 | `cp_word`, `cp_key_head`, `cp_proof_head`, `cp_policy_word` |
| `fp-core/src/out.rs` | 110 | `cp_line_of`, `cp_reason_of`, refusal/`input-unreadable` formatting |
| `fp-core/src/stage_state.rs` | 128 | the per-stage mutable state (17 fields, see below) |
| `fp-host/src/main.rs` | 557 | CLI, file reads, header checks, stage skeleton |
| `fp-host/src/usage.txt` | 97 | static usage text captured from the C++ reference |
| `fp-host/tests/core_test.rs` | 177 | 10 unit tests |
| `fp-host/tests/names_test.rs` | 43 | 2 consistency/coverage tests |
| `scripts/parity.sh` | 181 | S1 parity gate |
| `fixtures/` | ~6.9 MB | byte-for-byte example files, malformed inputs, goldens |

## Acceptance commands and results

```text
$ cd rust-nostd-verifier && cargo build --workspace
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.00s

$ cargo test --workspace
     Running unittests src/lib.rs (target/debug/deps/fp_core-...)
test result: ok. 0 passed; 0 failed; ...
     Running unittests src/main.rs (target/debug/deps/fp_host-...)
test result: ok. 0 passed; 0 failed; ...
     Running tests/core_test.rs (target/debug/deps/core_test-...)
test result: ok. 10 passed; 0 failed; ...
     Running tests/names_test.rs (target/debug/deps/names_test-...)
test result: ok. 2 passed; 0 failed; ...
test result: ok. 0 passed; 0 failed; ...   (doc-tests)

$ grep -rn "use std\|extern crate std\|static mut" fp-core/src/ && echo VIOLATION || echo NO_STD_OK
NO_STD_OK

$ grep -rn '^static ' fp-core/src/ && echo STATIC_FOUND || echo NO_STATIC_ITEMS
NO_STATIC_ITEMS
```

No-arguments parity (C++ `/tmp/tl_cpp_build/cp_verify` vs `target/debug/fp-host`):

```text
cpp_exit=2
rust_exit=2
STDOUT_IDENTICAL
STDERR_IDENTICAL
9147 bytes of stderr each
```

Full gate:

```text
$ ./scripts/parity.sh
parity: C++ reference: /tmp/tl_cpp_build/cp_verify
PASS no_args
PASS bad_option
PASS bad_bits
PASS bad_j
PASS bad_id
PASS bad_policy
PASS bits_above
PASS missing_key
PASS missing_policy
PASS bad_key_head
PASS short_key
PASS bad_proof_head
PASS short_proof
PASS missing_proof
PASS missing_leaf
PASS policy_version
PASS kl_length
PASS missing_request
PASS missing_y
PASS missing_entry_part
PASS plan_no_sub
PASS accepted example (C++ against golden_stdout.txt)
PASS tampered proof (C++ against golden_negative_tampered.txt)
PASS wrong commitment ID (C++ against golden_negative_wrong_id.txt)
PASS Rust stage stub: NOT CHECKED, no YES (full parity is S3)
parity: 25 passed, 0 failed
```

The 21 S1 cases compare **stdout, stderr and exit status** byte for byte after first checking that
C++ still matches the stored goldens in `fixtures/cli/`. The accepted example is the C++ `-q`
output against `fixtures/golden_stdout.txt`; the only normalized lines are the three
`---- stage ... ---- N thread(s), X.XXX s` headings, whose seconds differ between runs. Both
negative controls match their stored three-line goldens and exit 1.

## TL review fixes (A1-A4)

- **A1**: `docs/nostd-inventory.md` now marks `vf_input_files.h` as `是*`, with `cpConfRead()` host
  I/O and `cpWord`/`cpKeyHead`/`cpProofHead` in the core.
- **A2**: §7 now defines the S3 P0 gate as the closing four lines **plus** the `accounting:` numbers
  (`q_V=136088`, `least-round`, …) and text skeleton, all byte-identical. The old sentence that
  excused the accounting text was removed.
- **A3**: the hash row now says `tweak.h` is domain separation; the two counters are
  `blk::hash_calls_made` (`BLK_COUNT_HASH_CALLS`) and the `f2b` counter in
  `vf_earlier_hash_f.h`.
- **A4**: `fp-core/src/names.rs` has all 304 entries in file order. Each carries a
  `source: "verifier/src/...:line"` pointer and a `tests:` list of files under `verifier/tests`
  that mention it. The header records the three sources named by TL: `commitment_id_test.py`
  asserts `model-statement`; `what_a_yes_covers_test.py` asserts `policy`, `statement-range`,
  `statement-required` and `input-unreadable-*`; `known_answers/` contains hash/forest vectors and
  names `forest-calls`/`forest-trees` where it does. `fp-host/tests/names_test.rs` enforces the
  304-entry order and the presence of those notes.

## Points for TL review

1. **17th state field.** `StageState` has the TL list's 16 fields plus `run_version_word_fixed`
   (`vf_common.h:447`), the partner of `run_version_word`. Without it a stage reset would leave the
   version word in a half-fixed state. The module comment records this.
2. **`-plan` is a stub.** `-plan` with no subcommand reproduces the C++ usage fault; valid
   subcommands end `NOT CHECKED: internal-stage`. The S1 gate does not compare them, because C++
   performs real planning there. S2/S3.
3. **`cpPolicyHeld()` and odd-length request handling are deferred.** S1 reads `request` and `y`
   and implements `cpLengthHeld()` for regular files, but does not run the policy-vs-request checks.
   The S1 fixtures use the accepted example's valid exact-match request, for which
   `cpPolicyHeld()` rejects nothing; the gate is unaffected.
4. **`pol_word_u64()` is a line search.** It reads `lt` for `cpLengthHeld()` without the strict
   `blk::read_parameters` frame parser. S2 replaces it with the strict parser.
5. **Golden timing normalization.** `fixtures/golden_stdout.txt` is the full 105-line `-q` output,
   but the three stage headings contain wall-clock seconds. `parity.sh` normalizes only those.
   Everything else, including all `accounting:` lines and `result-v1`, is compared byte for byte.
6. **Fixtures are copies.** The example files are byte-for-byte copies; the `ID.txt` value is the
   example's. The malformed inputs are small local files (except `ivk-no-leaf/key.bin`, a copy).
7. **One C++ string was corrected by the goldens.** The `-j` fault is `THREADS_FORM` alone, not
   `"after -j comes <threads>; " + THREADS_FORM`; the first Rust version differed by 26 bytes and
   was fixed before the final run.
8. **C++ reference.** `/tmp/tl_cpp_build/cp_verify` was used. It is an Apple clang build from this
   checkout with `VF_SOURCE_DIGEST=93afdaf5…9595`; its accepted output matches the stored golden
   after timing normalization. `scripts/parity.sh` falls back to `/tmp/fp_cpp_build/cp_verify` or
   builds the reference itself.

## Stop point

S1 is complete and verified. Not starting S2; waiting for TL review.
