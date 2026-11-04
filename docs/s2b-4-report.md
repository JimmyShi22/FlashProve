# S2b-4 report: the frame

S2b-4 ports `blocks/frame/` and pays the three S1 debts that the frame needs: the `-plan`
subcommand's parsing, `cpPolicyHeld()`, and the strict `pol_word_u64` (`polWord`).

## 1. What landed

| Module | C++ source | Verifier content |
|---|---|---|
| `frame/parameters.rs` | `blocks/frame/parameters.h` | `GroupLine`, `StageChoice`, `Parameters`, `StrictLines`, `read_parameters`, `pol_word_u64` |
| `frame/fields.rs` | `blocks/frame/fields.h` | `Field`, `class_of`, `fields_of` |
| `frame/heads.rs` | `blocks/frame/heads.h` | `read_head`, `read_head_entry`, `parameter_file_digest`, `configuration_digest`, `published_id`, the four chain labels |
| `frame/req_frame.rs` | `blocks/frame/req_frame.h` | `layout_read`, `FrameArray`, `FrameLink`, `LayoutLines`, `req_frame` |
| `frame/derive.rs` | `blocks/frame/derive.h` | `FrameShape`, `TestSizes`, `Derived`, `setting_of`, `shape_of`, `solve_group`, `solve_test`, `derive_table`, `derive` |
| `numbers/plan.rs` (builder) | `blocks/numbers/plan.h:43-58,447-625` | mutable `Plan`, repeat/part/scope, `close`/`close_none`/`append`, `kind_of_round`, `Planned::names_of_the_format`, `same_setting` |
| `numbers/blocks.rs` | `blocks/numbers/blocks.h:46-268,361-1175` | `GroupSize`, `Analysis`, `GroupLoad`, `size_group`, `group_holds`, `scope_positions`, `positions_from_below`, `solve_stages`, `TableSize`, `size_recorded_table`, and every `plan_*` emitter (`send`, `bat`, `psc`, `lookup`, `rng`, `fold`, `cs`, `base`, `iopp`, `record`, `lin_*`, `link`) |
| `iop/req.rs`, `iop/req_rows.rs` | `blocks/iop/req.h`, `req_rows.h` | request shapes, loads, groups, faults and layout checks |
| `frame/lin_frame.rs` | `blocks/frame/lin_frame.h` | `LinLines`, `lin_lines`, `lin_rows_of`, `lin_group_bits`, `lin_sized`, `lin_size_of`, `lin_plan_first/shared/second`, `lin_require_sized` |
| `frame/link_frame.rs` | `blocks/frame/link_frame.h` | `LinkLines`, `link_lines`, `link_table`, `link_sized`, `link_plan` |
| `frame/wf_frame.rs` | `blocks/frame/wf_frame.h` | `WfShape`/`WfShapeLookup`, `wf_cut`, `wf_parts_of`, `wf_planes_of`, `wf_lines`, `WfSized`, `wf_sized`, `wf_plan` |
| `frame/wf_units.rs` | `blocks/frame/wf_units.h` | `WfUnit`, `wf_units_fault`, `wf_shape_of_units`, `wf_layout_fault`, `wf_shape_of_layout` |
| `iop/req.rs` (plan half) | `blocks/iop/req.h:306-407` | `ReqSizes`, `ReqSubPlan`, `req_plan` |
| `frame/files.rs` | `blocks/frame/files.h` | `Subproofs`, `stand_in_subproofs`, `frame_shape_of`, `table_tree_of`, `FilePlan`/`ChainPlan`, `Sized`, `sized`, `add_table_chains`, `file_proof/key/entry`, `merged` |
| `frame/key_fixed.rs` | `blocks/frame/key_fixed.h` | `KeyFixed`, `key_fixed`, `key_public_bytes`, `key_fault` |
| `frame/hiding_conditions.rs` | `blocks/frame/hiding_conditions.h` | `RangeCheck`, `TableUse`, `ReadAt`, `range_check_bits`, the four `hiding_conditions_missed*` functions |
| `frame/configure.rs` | `blocks/frame/configure.h` | `ProofVerdict`, `RequestFixed`, `Shapes`/`ShapesOf`, `Configured`, `configure`, `published_id`, `table_columns`, `Work` |
| `frame/check_key.rs`, `frame/check_entry.rs`, `frame/check.rs` | `blocks/frame/check_key.h`, `check_entry.h`, `check.h` | `KeyPublic`/`bind_one_time_chain`, `read_key_table_unproved`, `check_key_under`/`check_key`; the entry equivalents and `check_entry_if_tested`; `RequestPublic`, the four `bind_*`, `LinksResult`/`LinksCheck`, `ProofFacts`, `check_proof`/`check_proof_if_tested` |

## 2. The S1 debts

- **`-plan` parsing** (`fp-host/src/main.rs`): `id`, `accounting`, `arrays` and `request` now parse
  their command lines, options and files in the same order and with the same texts as
  `cpPlanMain()`. Where C++ would run a stage and print a plan, the port still ends `NOT CHECKED`
  (exit 5): the planners and `configure` are the remaining S2b-4 work, and a stub can never print
  `YES`. Six new CLI cases (`plan_id_argc`, `plan_accounting_asked`, `plan_request_short`,
  `plan_request_no_prompt`, `plan_request_bad_option`, `plan_bogus`) are compared with the C++
  reference byte for byte.
- **`cpPolicyHeld()`**: ported with `policyKind`, `acceptancePolicyIsExactMatch` and
  `PolicyNamed::is`; called after the request and y are read and before the proof file, only for
  whole-word statement files, as in C++. `pol_word_u64` now runs the strict parser first and scans
  `Parameters::rest` (or the whole text for a non-`version` fragment), matching C++'s `polWord()`.
- **Strict `pol_word_u64`**: the S1 line search over the whole file is gone; the frame parser
  strips the frame first, so a rejected `version`-prefixed file yields `None` for every name.

## 3. Evidence

`scripts/parity_frame.sh` now runs **29 checks: 29 passed, 0 failed**:

- `frame_parameters_vectors`: a C++ tool mutates `fixtures/config/policy.txt` in 49 ways and dumps
  every parsed field, the exact rejection text and the whole `rest`; the Rust replay matches all
  49, including the partial state a rejection leaves.
- `frame_layout_vectors`: a C++ tool parses the accepted `layout.txt` and 23 mutations of it (blank
  and comment lines, signs, leading zeros and spaces, CRLF, class/life rules, field counts,
  logarithms, block letters); the Rust `layout_read` matches all 24.
- `frame_derive_vectors`: a C++ tool runs `derive()` with the default `FrameShape` on the accepted
  parameters (a segment's group at `t = 218`, the last closing's five stages, the table's two
  distances); the Rust `derive` reproduces every size.
- Seven `cpPolicyHeld` cases (a changed `sT`, `C` or `cap`, and three `-policy` mismatches) are
  compared with the reference `cp_verify` byte for byte: stdout, stderr and exit status.
- `plan_emitters_vectors`: 17 C++ cases (SEND, BAT, PSC, lookups, RNG, FOLD, LOC, CS, BASE,
  IOPP, record, LIN first/shared, LINK, scopes, instances and the AT rule) dump every round and
  message; the Rust replay compares them field by field (187 rounds, 204 messages).
- `frame_sizes_vectors`: LIN (normal, one-time and no-split, five shape/refusal cases), LINK
  (accepted and two refusals), WF (two layouts and four refusals) and a synthetic `req_plan` are
  dumped with every code list, stage, tree size and every plan round/message; the Rust side
  reproduces all 5,852 lines.
- `frame_tree_sizes_vectors`: eight layouts of oracle messages pin `tree_sizes`, including the
  one-list marks and their running numbers.
- An independent read-only audit of all 32 plan emitters, 9 MayLay helpers and 12 plan-building
  helpers against `blocks.h`: **NO MISMATCHES**.
- `frame_files_vectors`: `sized(par, stand_in_subproofs())`, the three file plans and `merged`,
  with every size, code list, shape, chain, round and message, plus ten `key_fault` mutations.
  Two parameter files: the accepted one (whose table is too small for the stand-in, pinning the
  refusal chain sets) and `fixtures/config-standin/policy.txt` (the whole compact planning path:
  19,860 rounds, 16,294 messages, 3,864 key-public bytes).
- `frame_configure_vectors`: `configure` on the stand-in shapes, with seven cases (accepted; four
  cross-check refusals; the hiding `range-checks` refusal of the literal empty list; a layout
  refusal) and ten direct `key_fault` mutations, dumping every `Configured` field (sized summary,
  per-chain plans, merged accounting, `Work[3]`, `table_columns`, `fixed`, `range_checks`,
  digest, `key_fault`). The accepted configuration digest is
  `e9b96edbb42cfd5c73248c0fc7bbc3720285ab20736b3f1c0761b03aaabd34b2`.
- The three frame checkers are compile-complete with 42 early-path unit tests: header/tag/version,
  missing root/record, `key_fault`/`entry_fault` mutations, refused configurations, untested
  tables, plans that do not hold, `key_public` program faults, and a missing first-chain salt
  reaching the real chain builders. Accepted files need the prover engine (S3).
- `cargo build --workspace`, `cargo test --workspace` (202 passed at this point) and the no_std
  scan pass. Independent read-only audits of the plan emitters (53 functions),
  configure/hiding (41 functions) and the three checkers (31 functions) all returned
  **NO MISMATCHES**.

The S1 gate (`scripts/parity.sh`) now runs **31 passed, 0 failed**: the six new `-plan` usage cases
(`plan_id_argc`, `plan_accounting_asked`, `plan_request_short`, `plan_request_no_prompt`,
`plan_request_bad_option`, `plan_bogus`) are compared with the C++ reference. `parity_base.sh` is
still **37 passed, 0 failed**, and the S2a gates (`parity_field`, `parity_hash`, `parity_numbers`)
still PASS.


## 4. Deviations and deliberate omissions

- Prover-only writers and engines are omitted (`make_key*`, `make_entry*`, `sized_table`,
  `hiding_conditions_missed_by_the_file`, the test-only constructors). `stand_in_subproofs` is
  ported because the file/configure parity tools use it.
- `ShapesOf` in C++ is a plain function pointer whose callees read program globals; the Rust
  `configure` takes the same shapes as data, and no purity is claimed.
- The host still ends `-plan` at `NOT CHECKED`: `configure` and the planners exist, but the host
  does not yet print a plan, and a stub must never print `YES`. Wiring the `-plan` output is S3.
- `layout_read` accepts the same spellings as C++ `sscanf` (signs, leading zeros) and rejects the
  same lines; the parser is byte-oriented and never normalizes.
- A Rust `VerifierRounds` owns its reader and session, so two channels cannot be live at once.
  `check::continue_chain` moves the first chain's `Statement`/`TreeBook` into the second, and
  `check::lin_second_verify_with` replicates `lin_second_verify`'s body around them; the
  C++ `stands_on` assertions that depend on both channels live are structurally omitted (documented
  at the call sites). `link_verify` takes the notes vector by value, so LINK's notes do not return
  to `check_entry_under`'s caller; this does not affect verdicts.
- `VerifierRounds::why()` now returns `Option<&'static str>` (every recorded reason is static), so
  the checkers can keep the reason after a context is dropped; `PublicBytes for Vec<u64>` was added
  for `RequestPublic::identifiers`.

## 5. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve
rust-nostd-verifier/scripts/parity_frame.sh
rust-nostd-verifier/scripts/parity_base.sh
rust-nostd-verifier/scripts/parity.sh
```

## 6. Still open for S3

- The verifier's real `ShapesOf` (the model/sub-proof shape builder in `verifier/src/vf_segments.inc`)
  and therefore the frame comparison against `fixtures/plans_dump.txt` for the accepted example.
  S2b-4 validates `configure` on `stand_in_subproofs` and the C++ `cp_frame` path instead.
- Full-file `check_key`/`check_entry`/`check_proof` acceptance: the Rust checkers are ported, but
  honest files need the prover engine, which is S3's harness.
- The end-to-end `YES` and `result-v1` alignment, the negative controls, and the zkVM stages.
