# S2b-2 and S2b-3 report: the algebraic, fold, commitment and lookup blocks

This report covers the two waves after the S2b-1 foundation:

- **S2b-2** — the algebraic and fold blocks: `relation`, `tensor`, `hp`, `psc`, `summand`,
  `mask`, `line`, `bat`, `batt`, `batt_shown`, `split`, `fold*`, `cs`, `laid`, `single_rows`,
  `iopp`, `base_case`, and the verifier-side `context`/`send` that those blocks call.
- **S2b-3** — the commitment and lookup blocks: `foldeq`, `lin`, `link`, `member`, `lkp`, `rng`,
  `wf`.

Both waves port the verifier's side. The prover's engine/GPU/coins machinery is not ported; where
a shared function also serves the prover, only its arithmetic and verifier-visible behaviour are
kept.

## 1. S2b-2: what landed

| Module | C++ source | Verifier content |
|---|---|---|
| `iop/relation.rs` | `blocks/iop/relation.h` | `Statement`, oracles, groups, claims (`Row`, `Run`, `Term`, `Unit`), `GroupLayout`, `RunInput`, `add_to_group_row`, `RowsAside` |
| `iop/tensor.rs` | `blocks/iop/tensor.h` | `Tensor`, `Form`, frozen parts, fix/fold/write-out arithmetic, `laid`/`batt` interfaces |
| `iop/hp.rs` | `blocks/iop/hp.h` | `Weight`, `hp_form`, `HidingPolynomial`, polynomial helpers |
| `iop/psc.rs` | `blocks/iop/psc.h` | `psc_vars`/`psc_masks`/`psc_size`/`psc_rows`, `psc_verify` |
| `iop/summand.rs` | `blocks/iop/summand.h` | `PointClaim`, `SumClaim`, `Summand`, `SumcheckProver` shape |
| `iop/mask.rs` | `blocks/iop/mask.h` | `MaskSlot`, `MaskTerm`, `SampleReceipt`, `MaskLedger` |
| `iop/line.rs`, `iop/split.rs` | `line.h`, `split.h` | the two claim reductions, verifier side |
| `iop/bat.rs`, `iop/batt.rs`, `iop/batt_shown.rs` | `bat.h`, `batt.h`, `batt_shown.h` | batching, BATT, BATT-shown |
| `iop/fold.rs`, `iop/fold_algebra.rs`, `iop/fold_rounds.rs` | `fold.h`, `fold_algebra.h`, `fold_rounds.h` | FOLD's claims, hiding polynomial and verifier rounds |
| `iop/cs.rs` | `blocks/iop/cs.h` | the code switch: target checks, lift/pieces, `switch_rows`, `switch_verify`/`cs_verify` |
| `iop/laid.rs` | `blocks/iop/laid.h` | matrix layout checks and `laid_tensor`/`laid_form` |
| `iop/single_rows.rs` | `blocks/iop/single_rows.h` | `SingleRows`, `group_as_run`, symbols/openings |
| `iop/context.rs` | `blocks/iop/context.h` (verifier side) | `TreeBook`, `OracleNotice`, `Opened`, `VerifierContext`, `receive_oracles`, `read_opened` |
| `iop/send.rs` | `blocks/iop/send.h` (verifier side) | `SampleCube`/`Send::pad`, `Send::form`, `send_verify` |
| `iop/iopp.rs` | `blocks/iop/iopp.h` | stages/faults, last rows, `iopp_verify` |
| `iop/base_case.rs` | `blocks/iop/base_case.h` (verifier side) | `BaseMask`, `base_mask_notice`, `base_shape_check`, `base_verify` |
| `numbers/round_names.rs` | `blocks/numbers/round_names.h` | the format's round names |

`context.rs` and `send.rs` are verifier-side dependencies of the listed blocks; they were added in
this wave because FOLD/CS/IOPP/BASE cannot be checked without them. SEND's prover half and the
engine/coins-dependent functions remain out of scope.

## 2. S2b-2: evidence

C++ vector tools, each built from the checkout's headers and compared with its fixture:

- `tensor_vectors` — Tensor/Form construction, dense slices, fix/fold, write-out.
- `hp_fold_vectors` — Weight/HidingPolynomial/fold algebra and `FoldProverRounds`/`FoldVerifierRounds`.
- `fold_output_vectors` — `fold_output` over hand-built rows.
- `iop_core_vectors` — mask ledger, statement/layout, BAT, laid, single rows, BATT.
- `iop_data_vectors` — mask, laid, BAT, BATT, PSC data/arithmetic.
- `components_vectors` — mask, group layout, BAT carry, BAT rows, BATT claim/row, laid forms, pads.
- `send_vectors` — `Send::form` on a two-table cube, both answers, including the `front()` factor.

At the approved S2b-2 commit (`534ad9b0`) `scripts/parity_base.sh` reported **23 passed, 0
failed** — 10 C++ fixture diffs, 10 Rust replay tests, the workspace build/test, and the no_std
scan. The `send_vectors` tool, fixture and test were generated immediately after that commit and
are committed in this push as the S2b-2 follow-up; the current gate includes them. The S1 gate
(`25/25`) and the S2a gates (`parity_field`, `parity_hash`, `parity_numbers`) still pass.

## 3. S2b-3: what landed

| Module | C++ source | Verifier content |
|---|---|---|
| `iop/foldeq.rs` | `blocks/iop/foldeq.h` | committed-table fold and column checks: `VectorLay`, `IndexShape`/fault/priced table, `IndexRecord`/`PublicBytes`/`IndexReader`, `record_value`, `block_sums`, `FoldedWant`, `FoldeqShape`, `foldeq_columns_verify`, `foldeq_require`, `foldeq_verify` |
| `iop/lin.rs` | `blocks/iop/lin.h` | the three-part linear protocol (`LinShape`, `LinClaim`, `W_c`/`G_u`/`Omega`, the second-part tie, proximity end), `lin_fault`, `lin_verify` |
| `iop/link.rs` | `blocks/iop/link.h` | leaf-anchor table equality: `LinkShape`, `public_fault`/`link_fault`, `link_message`/`link_bind`, `link_lists`, `Link::verify`, `steps_verify`, `test_verify`, `link_verify` |
| `iop/member.rs` | `blocks/iop/member.h` | one request's part of LIN: `member_claim`, `member_weights_on_rows`, `member_pending_row`, `member_rows_fit`, `member_first_verify` (BATT batching into LIN's first part) |
| `iop/lkp.rs` | `blocks/iop/lkp.h` | product-tree lookup: public inputs and `lkp_fault`, summands, verifier rounds, the key claim on the sent digits, masks |
| `iop/rng.rs` | `blocks/iop/rng.h` | approximate range check: `RngShape` and faults, `rng_lookup` layout, weights/plan checks, `rng_theta`, the batched row, lookup masks |
| `iop/wf.rs` | `blocks/iop/wf.h` | in-range proof: `WfLookup` parameters (`wf_lookups`, `wf_layout`, `wf_planes_at`, `wf_weights_on_rows`), `wf_fault`/`wf_start_check`, `wf_rows_verify`, `wf_verify` |

The shared infrastructure that these modules call (`context`, `send`, `iopp`, `cs`, `foldeq`'s index
and fold helpers) is the S2b-2 port listed above. As in S2b-2, only the verifier's side is ported;
the prover engines, coins, layouts and `*_prove` entry points are omitted. The deviations the
modules document in their headers are repeated in section 5.

## 4. S2b-3: evidence

Six C++ vector tools, each built from the checkout's headers and compared with its fixture byte for
byte, replay the wave's verifier-visible behaviour:

- `foldeq_vectors` — index shapes, records and readers, table layouts, the folded row, record and
  column claims, and the record/public/key/index/fold faults.
- `lin_vectors` — LIN's three parts: messages, tables, rows, coefficients, the binding and 17
  faults.
- `link_member_vectors` — LINK's equality rows, notices, lists and steps, MEMBER's stretched
  weights and pending row, and 9 faults.
- `lkp_vectors` — public inputs, rows, tables, padding, masks, is-padding, blocks, shapes, key
  claims, weights, cubes, orders, summands, counts, live blocks and on-block, plus fault coverage
  for `lkp_fault`: the `fault=` field of every `LKP_PUBLIC`, and 45 `LKP_FAULT` cases (3 accepted,
  42 rejected across all 27 distinct faults) that dump the whole mutated lookup.
- `rng_vectors` — shape and public faults, the lookup's layout, weights and plan checks, Theta, the
  batched row and the planes' coefficients.
- `wf_vectors` — lookups, planes, weights, starts and rows, and 25 faults.

`scripts/parity_base.sh` now runs **37 checks: 37 passed, 0 failed** — 17 C++ fixture diffs (11
from S2b-1/2 and 6 from S2b-3), 17 Rust replay tests, the workspace build and test, and the no_std
scan. The Rust replay tests report: `foldeq_vectors` 1 passed, `lin_vectors` 1 passed,
`link_member_vectors` 1 passed, `lkp_vectors` 1 passed, `rng_vectors` 1 passed, `wf_vectors` 3
passed. `cargo test --workspace` reports **45 passed**. The S2a gates (`parity_field`,
`parity_hash`, `parity_numbers`) and the S1 gate (`parity.sh`, 25/25) still PASS.

An independent read-only guard audit compared 266 guard sites (every condition carrying a
`foo.h:<line>` comment, plus uncommented guards matched function by function) in `member`, `link`,
`wf`, `rng`, `foldeq` and `lin` against the C++ headers, operator for operator: **NO MISMATCHES**.
`lkp.rs` was excluded from that pass because its `lkp_fault` was audited directly and its 27 fault
messages are all exercised by the vectors.

The new vectors caught a real defect before review: `lkp_fault` had two inverted overlap checks.
At `lkp.h:324` (key blocks) and `lkp.h:344` (table parts), C++ faults when `meet` is true (the
blocks overlap), while the port faulted when it was false. `rng_vectors`' `LOOKUP_FAULT a` first
exposed the table case (a valid shape was rejected), and `lkp_vectors`' `key_blocks_overlap` and
`table_overlap` exercise the faulting direction. Both checks are fixed in `iop/lkp.rs` with
source-line comments; no existing fixture line changed, and the lkp fixture gained the `LKP_FAULT`
cases for coverage.

Five S2b-2 defaults were corrected in the same push, because they are observable as soon as a
caller default-constructs the type: `BaseMask.id`, `Switched.g`, `FoldShape.code`/`mask_code`,
`IoppStage.code`/`mask_code` are `NONE_ID` in C++ but were `0` from Rust's derive, and
`Tensor::default()` is `E::one()`, not zero (`tensor.h:70`; `Tensor::zero()` is now explicit).
They are in the S2b-2 follow-up commit, together with the `send_vectors` files, not in the S2b-3
diff.

## 5. Deviations and deliberate omissions

- Verifier-only: `ProverContext`, the engine (CPU/GPU tables), `Coins`, prover drafts, prover
  self-checks and all `*_prove`/`*_prove_on_shape` entry points are not ported. Shared arithmetic
  and the data that a verifier reads are ported.
- C++ templates over the challenge field are specialised to `E` in the channel-level blocks;
  `hp`, `fold_algebra` and `fold_rounds` stay generic over a small `ChallengeField` trait so their
  C++ tests' small fields can be replayed.
- `shared_ptr<const vector<T>>` is `Rc<Vec<T>>`; `std::map` is `BTreeMap`; `std::function` is
  `Box<dyn Fn>`.
- The channel methods take an explicit `&mut HashCalls`; the C++ globals are not reproduced.
- Fatal C++ guards (`BLK_REQUIRE`) are Rust panics; proof-dependent failures return `false` and
  leave the channel rejected. `non_snake_case` is allowed in `iop/` so parameter names `S`, `V`,
  `T`, `G`, `L` keep their C++ spelling beside the source comments.
- The prover's table/engine layouts (`Table`, `OracleDraft` fields beyond their public shape) are
  absent. `OracleNotice` is the verifier's form of a sent oracle message.
- S2b-3 boundary deviations, all forced by the port's ownership (the channel owns its session and
  keeps its fate private): `IndexReader::read` takes the whole `VerifierRounds` instead of a
  `Reader` plus a `VerifierSession`; `Link::verify` takes the plan as `Rc<Planned>` and clones the
  two records out of the chain's first query; `member_first_verify` lends `HashCalls` explicitly.
  Where C++ asks a rejected channel in a destructor, the port reports rejection explicitly through
  `LkpKeyClaim`, `RngOutput` and `WfPending::channel_rejected` (a rejection that happens after the
  verifier returned true is not seen; no honest run reaches that point). `rng_theta` draws the
  entries before `require_combinations` because `close_bits` borrows the channel mutably; the two
  calls touch different state, so the order is observable only where both versions end the process.
  `foldeq` compares `Plan::same_setting` field by field because `numbers/plan.rs` has no equivalent.
  The frame types `TestedTable`, `UnprovedTable`, `IfTested` and their pass-keys are left to the
  S2b-4 frame layer; `TableRead` carries the optional `Setting` such a tested table would hand in.

## 6. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve
rust-nostd-verifier/scripts/parity_base.sh
rust-nostd-verifier/scripts/parity_field.sh
rust-nostd-verifier/scripts/parity_hash.sh
rust-nostd-verifier/scripts/parity_numbers.sh
rust-nostd-verifier/scripts/parity.sh
```

## 7. Still open for S2b-4 and S3

The frame and file layers (`frame/{parameters,derive,configure,files,heads,hiding_conditions}`,
`check_*`), the `-plan` stub, `cpPolicyHeld`, strict `pol_word_u64`, and the end-to-end S3 run.
The verifier-side blocks above are the inputs to those checks; S3 is the first stage that runs
them against the accepted example and the negative controls.
