# S2c report: the verifier's sub-proofs

S2c comes in two waves:

- **S2c-1** — the shared foundation: the public table gate, `vf_common` core, the transcript
  channel, the sub-proof engine, smallness/packing/test, the lookup argument/helpers and the
  sumcheck variants.
- **S2c-2** — the three sub-proofs (attention, layers, output head) and the join: the stage
  statement and layout, the stage context around the layer and head sub-proofs, the request frame
  and its rows, the layer and head plans and checks, and the request chain that ties them together.

Both waves are complete; `scripts/parity_subproof.sh` reports **31 passed, 0 failed** and the
workspace runs **228 tests, 0 failed**.

## 1. What landed

| Module | C++ source | Content |
|---|---|---|
| `verifier/tables.rs` | `cp_verify.cpp:181-215,1301-1303,1412-1428,1592-1610,2004-2011`; `vf_attention_shape.h:203-212` | `TableParams`, `sigmoid_table_entry`, `sigmoid_clamp_table_entry`, `gate_table_entry`, `silu_table`, `sigmoid_table`, `rope_table`, `exp_table`, `table_digest` (H(72; ·)), `check_table_digests` |
| `verifier/engine.rs` | `vf_subproof_engine.h` | `power_of_two_at_least`, `HRow`/`HTree`/`Ent`/`Aff`, `HFork` (slots, `hide`/`shown`, `public_part`, `claims_in`, `push`, batching `theta`, `kap_at`/`kap_take`/`kap_all_taken`, `owe`, `lin`, `settle`), `trim_l`/`fill_l`, product levels (`read_product_level_rounds`, `hand_down`, `layer_object`) |
| `verifier/packing.rs` | `vf_smallness_packing.h` | `LRAD`/`LANES`/`KCAP`/`RADB`, `ShP`, `place_p`, `PlP`, `PlaceF`, `same_place_f`, `tie_left`/`tie_right`, `eq_plain_f`, `UnscaledEqIterator` |
| `verifier/matrices.rs` | `vf_smallness_matrices.h` | `TMat`, `Tail` (`fold_columns`) |
| `verifier/segment.rs` | `vf_subproof_segment.h` (the frame-free part) | `N2`, `Tail2`, `t2_add_n`/`t2_add_p`/`t2_plan`/`t2_fill_l`, `Run2`, `t2_lin`, `EqRun`, `eq_low`/`eq_low_at` |
| `verifier/lookup.rs` | `vf_lookup_argument.h`, `vf_lookup_helpers.h` | `HPiece`, `HCallZ`, `HFun`, `HForest` (shape, padding counts, `forest_*` claims, join, plane claims), `place_z`, `u_ent`, `HStack`, `stack_rounds`, `order_forest_range` |
| `verifier/sumcheck.rs` | `vf_sumcheck_psc.h`, `vf_sumcheck_receive.h`, `vf_sumcheck_token.h`, `vf_sumcheck_attention.h` | `Psc`, `psc_begin`/`psc_round`/`psc_ends`/`psc_row`, `RoundForm`, `round_in`, slot counts, `TokenSumcheckState` (`tsc_rounds`/`tsc_in`), `Degree3SumcheckState` (`sc3_*`), `VariedDegreeSumcheckState` (`scd_in`) |
| `verifier/smallness.rs` | `vf_smallness_test.h`, `vf_smallness_test_members.inc` | `HTailF2`: `shape`/`pieces_f`, `add_trees`, `transcript`, `coefficients`, `fold_sums`, `objects` (join, bits, ties, reads), `self_test`, `tile_self_test`, `close_funs`/`funs_held`, `plan_rounds`, equation and claim counts |
| `verifier/attention_shape.rs` | `vf_attention_shape.h` | `CLAMP`, `TenAt`, `ten_cell`, block/point helpers, `ACfg`, `AsSeg` (`S_RM`..`S_IX`), `AFork::shape`, `bind_tau`, `table_words`, `cover`, `afork_shape_hid` |
| `verifier/attention_plan.rs` | `vf_attention_check.h` (planning half) | `AttentionRounds`, `attention_sc3`, `attention_scd`, `plan_attention_own`/`plan_attention_end` |
| `verifier/attention_check.rs` | `vf_attention_check.h` (checking half) | `AttentionSeam` (`shape`/`i_u3`/`small_elems`/`plan`/`start`/`transcript`/`batch`/`objects`/`finish`), `AttentionSubProofInputs`, `AttentionSubProof::plan`, `AttentionSegment`, `OpenSegment` (the test seam) |
| `verifier/attention_run.rs` | `vf_attention_check.h` (`AttentionSubProof::run`) | the whole attention walk: lookup, Y/values/planes claims, score/value/index claims, range check, merge, closing equation |
| `verifier/weights_layout.rs` | `vf_weights_layout.h` | `WsShape`, `ws_set_moe`, `WsGrp`, `WsUnit`, `WsLay::{e_,a_,add,build}`, `WsFac`/`WsClaim`/`WsRowFac`/`WsRecClaim`, `ws_claim_shape`, `ws_eps_t`, `ws_row_part`, `ws_gamma_add`, `WsForkOut`, `ws_fork_end` |
| `verifier/weights_merge.rs` | `vf_weights_merge.h` | `WsMerged`, `ws_fork_merge`, `ws_fork_lin`, `ws_fork_slots` |
| `verifier/weights_pending.rs` | `vf_weights_pending_claim.h` | `WsPending`, `ws_pending` |
| `verifier/norm_digit_rows.rs` | `vf_norm_digit_rows.h` | `led_ns/nr/np/no/lines/nrh/mu`, `LedKind` for `E`/`Aff`, `Row5`, `row5`, `led_carry5`, `led_lines5`, `led_products5` |
| `verifier/stage_layout.rs` | `cp_verify.cpp:1353-1900` (statement, `layout()`) | `Hdr`, `StOwn`, `LineIter`, `word_line_form`, `digits_beyond_scan`, `scanned`, `pol_word`, `parse_header`, `PolScan` (`pol_prescan`/`pol_skeleton`/`pol_scan`), `Ten`, `Seg`, `CallD`, `KindD`, `Lay`, `layout`, `set_tau` |
| `verifier/stage_context.rs` | `cp_verify.cpp:1353-1395,1552-1840`; `vf_attention_check.h` inputs | KL constants (`KW_ = 13`, `LKQ..LKRP`), `kl`, `kl_m`, `kl_rp`, `kl_sh`, `rope_c`, `kl_checks`, `build_tails`, `token_factor_taken`, `token_factor_units`, `build_ws_lay`, `Hl`, `build_hl`, the no-wrap h9 conditions, `WEIGHT_WIDTH_BITS = 13`, `WEIGHT_BOUND = 1024` |
| `verifier/layers_rounds.rs` | `prover/prover/plan_rounds.h` | `LayerRounds`, `plan_product_layer`, `plan_token_sumcheck`, `plan_layer_own` |
| `verifier/layers_plan.rs` | `vf_layers_plan.inc`; `cp_verify.cpp:1996-2093` | `Reads`, `reads_of`, `LayerPlanSizes`, `plan_sizes`, `HPlan2`, `plan_layers`, `plan_layer_moment`, `t2_same_shape` |
| `verifier/layers_check.rs` | `vf_layers_check.inc` (`runForkHidG2`) | the layer walk: lookup forest, U3 tables, the two token sumchecks, the batched sumcheck, the gated products, the weight claims, the norm digit rows, the range check, the closing equation |
| `verifier/head_rounds.rs` | `prover/head/plan_rounds.h`; `prover/hiding/token_plan.h` | `HeadRounds`, `plan_token_sum`, `plan_head_own`, `plan_head_end` |
| `verifier/head_plan.rs` | `vf_output_head_plan.inc` | `HPlanH2`, `plan_head`, `HPlanH2::plan_moment` |
| `verifier/head_check.rs` | `vf_output_head_check.inc` (`runForkHidH2`) | the head walk: final norm, logits, acceptance policy, the one weight claim and its merge |
| `iop/req.rs` | `blocks/iop/req.h:434-732` (verifier side) | `ReqFrame` (shape/groups/link/where/plain/group), `req_first`/`req_later`/`req_close`/`req_finish`; the prover side is omitted |
| `iop/req_rows.rs` | `blocks/iop/req_rows.h:104-169` | `ReqTerm`, `ReqEquation`, `req_row` (the shared equation-to-`Row` builder) |
| `verifier/request_chain.rs` | `vf_request_chain.h` | `LinkHook`, `ChainCheck` (`first`/`later`/`close`/`finish`), `chain_verify` |
| `verifier/segments.rs` | `vf_segments.inc` (frame-free parts) | `LinkKind`, `LinkH`, `link_list_fault` (`plan-head`/`plan-link`/`plan-shape`), `pending_row_h` |

## 2. Evidence

- `scripts/parity_subproof.sh`: **31 passed, 0 failed**:
  - C++ tool/fixture comparisons: `common`, `table`, `subproof`, `attention`, `attention_plan`,
    `weights`, `layout`, `context`, `req_chain`, `layers_plan` (and its `head` mode); each builds a
    tool from the checkout's headers and compares its output byte for byte with its fixture;
  - Rust replays: `common_vectors`, `transcript_tests`, `table_vectors`, `subproof_vectors`,
    `subproof_tests`, `attention_vectors`, `attention_plan_vectors`, `attention_run_tests`,
    `weights_vectors`, `weights_tests`, `layout_vectors`, `context_vectors`, `req_chain_vectors`,
    `layers_plan_vectors`, `head_plan_vectors`, `layers_run_tests`, `head_run_tests`;
  - `cargo build --workspace`, `cargo test --workspace` (**228 passed, 0 failed**) and the
    `fp-core` no_std scan (`NO_STD_OK`).
- `table_vectors`: the C++ tool includes `cp_verify.cpp` as a translation unit and calls the actual
  static table functions and `earlier_hash_h_digest`; it dumps all 65,536 SILU entries, 65,536 SIG
  entries (the accepted model has `NE = 4`), 8,192 RoPE entries and 2,307 softmax entries, their
  H(72; ·) digests, the policy's 32 digest words and the accept/reject results. The Rust replay
  matches every integer entry and digest; flipping one word of each expected digest yields
  `table-digest-silu`, `table-digest-sigmoid`, `table-digest-rope`, `table-digest-exp` in both.
- `subproof_vectors` (`scripts/cpp_vectors/subproof_vectors.cpp`): the C++ tool instantiates the
  header-only parts and dumps 96 records, byte for byte compared with
  `fixtures/subproof_vectors.txt`:
  - the engine: `powerOfTwoAtLeast`, `Aff`'s addition/subtraction/scaling, `HFork`'s
    `hide`/`push`/`settle` (including the `internal-slot-unused`, `internal-slot-twice`,
    `internal-L-index` and `internal-L-row` refusals), `kapAt`/`kapTake`, and `uEnt`;
  - packing: `placeP`, `tieLeft`/`tieRight`, `eqPlainF`, `UnscaledEqIterator`, `samePlaceF`;
  - the lookup forest: `forestShape`'s sizes and placements, `forestPubRun`/`forestPubAsk`
    (including `pt-pub-forest` and `forest-only-padding-B`), `forestElems`/`forestLins`,
    `forestPlaneCols`, `orderForestRange`, `padKey`, `emptyKeys`/`padding`, `placeZ`'s pieces and
    `pub` counts;
  - the smallness plan: `shapeF`/`piecesF` on a synthetic matrix, `addTreesF`'s tree list and
    `tabFirst`/`tabLen`, the `T2D0`/`T2D1` lookup calls and the tie weights;
  - the sumchecks: `roundValues`/`sumcheckSlots`/`layerSlots`/`tscSlots`/`sc3Slots`, and `pscRow`
    on a hand-built `Psc` (the form over `hp_form`, the U coefficients' mask slots, the kept form
    and the constant).
- `fp-host/tests/subproof_tests.rs` runs the transcript-driven parts on a real `VerifierRounds`:
  the full `HTailF2::transcript` (RNG, commitment, the 31 tie sumchecks, 13 key levels, 11 table
  levels, the leaves and the bits) reaches the end with the planned slot count equal to
  `smallElems()`; `psc_begin`/`round_in`/`psc_ends`/`psc_row`, `stack_rounds`, `tsc_in`, `sc3_in`,
  `sc3_row` and `scd_in` all complete on hand-built plans. The chain itself is replayed against C++
  in `rounds_vectors.rs`.
- **Attention** (`attention_vectors`, `attention_plan_vectors`): the C++ tool builds the shape, the
  placement records and the planned rounds from a synthetic configuration; the Rust replay matches
  every field and `rounds_vectors`-style record. `attention_run_tests` then runs the whole walk on a
  real `VerifierRounds` with a zero proof and the planned rounds; it reaches the end with
  `nClaim == nLin`, the range check's coefficients drawn once and both lookup groups run.
- **Weights and norm rows** (`weights_vectors`, `weights_tests`): the C++ tool dumps the weight
  layout (`WsLay` units and groups), the merge/pending claim and the norm digit rows; the Rust
  replay matches every integer and the `ws_pending` refusals by name.
- **Stage statement, layout and context** (`layout_vectors`, `context_vectors`): the C++ tool calls
  the real `polPrescan`/`polSkeleton`/`polScan`/`parseHeader`/`layout`/setTau and then the KL,
  tails, `WsLay` and output-head layout code; the fixtures compare the statement parse, the layer
  layout, the KL words, every `Tail`/`TMat`, the weight units and the head's calls, forest and
  `tauFE` table item by item.
- **Request frame** (`req_chain_vectors`): the C++ tool proves the toy requests of
  `blocks/iop/tests/req_rows_cases.h` with the library's own prover and dumps the shape, layout,
  equations, plan and both proofs as bytes. The Rust frame (`ReqFrame`, `req_row`, `ChainCheck`,
  `chain_verify`) accepts the honest proofs through both the hook route and the call route and
  rejects every hostile run: another weight, a proof of a false target, and every run with a
  segment's `close()` or its last commit point left out. A 24-item fault battery (malformed shapes
  and layouts) compares the `req_fault()`/`req_layout_fault()` names item by item.
- **Layer and head plans** (`layers_plan_vectors`, `head_plan_vectors`): a C++ tool reproduces
  `vf_layers_plan.inc`'s per-group block and `vf_output_head_plan.inc` on the fixture policy and
  KL.bin, and dumps every `HPlan2`/`HPlanH2` field: the array list with its `T2` maps and placement
  records, the matrix list after `shape`, the U3 length, the message-slot count, the claim counts,
  the batched-sumcheck rounds and the sizes of the layer and head rounds. The Rust `plan_layers` /
  `plan_head` reproduce all of it item by item, including `borderCmpF`.
- **Layer and head checks** (`layers_run_tests`, `head_run_tests`): with the plan built by
  `plan_layer_moment`/`plan_head::plan_moment` from the fixture files, both walks read a zero proof
  on a real `VerifierRounds` to the end; the cursor accepts every round in the planned order, the
  channel's `ok()` holds, and the run reports exactly the planned claim and slot counts
  (`nClaim == nLin`, `ns == plan.ns`); the range check's self-tests, the per-slot self-test, the
  tiling self-test and the merge's end value all pass.

## 3. Deviations and deliberate omissions

- `libm::rint` stands in for C's `nearbyint` (ties to even under the default rounding mode);
  `libm::round` is C's `round`. The tables are floating-point derivations, but the format fixes
  them by the 32 digest lines, and every entry is compared as an integer.
- The C++ table tool reproduces the `ropeC` lambda and the attention softmax loop because they are
  not addressable from outside; it calls the actual static SILU/SIG entry functions and
  `earlier_hash_h_digest`.
- `check_table_digests` owns a local `HashCalls`; integration into a stage must fold these four
  digests' `f2b` counts into the run's accounting (`q_V`), which is S3's wiring.
- The gate reads `eg`/`smax`/`gcl` from the parameter tail it is given; duplicate or out-of-order
  optional lines are the strict policy scan's rejection, not the gate's.
- **The frame-backed segment seam is S3's wiring.** `LinkCtx`, `currentSegment`, the frame-backed
  `rootInH`/`t2Batch`/`doorH` and `rowWeights`/`doorH`'s equation construction are not installed:
  the checks take the same `Tr` and the `SegmentGate`/`AttentionSegment` seam that the attention
  port established, and `OpenSegment` is the test seam. `ChainCheck` and the request frame are
  ported and validated, so S3 only has to bind the seam to the chain.
- The C++ test harness's prover-value support (`HFork::valuesF`, `judged`, `judgeAll`, `take`,
  `valueOf`, `TestProverValues`) and the claim section names are omitted: no verifier decision
  reads them. `HFork::section` is absent for the same reason.
- `ShP::J` is 1 for every shape the programs make; `place_p` asserts it rather than defining the
  C++ division-by-zero case.
- `HForest` keeps the call metadata and returns each call's `alpha`/`zk`; the caller that owns the
  `Call`s writes them back (`HTailF2::transcript` does), because a Rust struct cannot point into
  its caller.
- The C++ checks carry `std::function`-captured forms; the port precomputes each panel's factors
  into vectors, because a Rust closure cannot borrow the fork, the tables and the claims list at
  once. The values are identical.
- The layer and head walks are validated on real plans with a zero proof (the attention lane's
  standard), not on a full C++ proof: the end-to-end proof path is S3's. The plan vectors, the
  round order enforced by the cursor, and the checks' own self-tests are the parity evidence here.
- `vf_segments.inc`'s driver (`buildLinksH`/`runLinksH`) needs the stage's sub-proof plans and the
  frame-backed seam; the frame-free parts (the link-list checks and `pendingRowH`) are ported, the
  driver is S3's.

## 4. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve
rust-nostd-verifier/scripts/parity_subproof.sh
```

## 5. Still open for S3

The stage bodies (`run_stage`), the real-model `ShapesOf`, the frame/segment wiring
(`LinkCtx`/`rootInH`/`t2Batch`/`doorH`/`rowWeights`), `buildLinksH`/`runLinksH`, end-to-end
`YES`/`result-v1` and the negative controls.
