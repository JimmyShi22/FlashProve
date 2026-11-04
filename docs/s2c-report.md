# S2c report: the verifier's sub-proofs

S2c comes in two waves:

- **S2c-1** — the shared foundation: the public table gate, `vf_common` core, the transcript
  channel, the sub-proof engine, smallness/packing/test, the lookup argument/helpers and the
  sumcheck variants.
- **S2c-2** — the three sub-proofs (attention, layers, output head) and the join.

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

## 2. Evidence

- `scripts/parity_subproof.sh`: **11 passed, 0 failed** — the three C++ tool/fixture comparisons,
  the five Rust replays (common, transcript, tables, sub-proof vectors, transcript-driven
  sub-proofs),
  the workspace build/test and the no_std scan.
- `table_vectors`: the C++ tool includes `cp_verify.cpp` as a translation unit and calls the actual
  static table functions and `earlier_hash_h_digest`; it dumps all 65,536 SILU entries, 65,536 SIG
  entries (the accepted model has `NE = 4`), 8,192 RoPE entries and 2,307 softmax entries, their
  H(72; ·) digests, the policy's 32 digest words and the accept/reject results. The Rust replay
  matches every integer entry and digest; the accepted policy's `tsilu*`/`tsig*`/`trope*`/`texp*`
  lines match, and flipping one word of each expected digest yields `table-digest-silu`,
  `table-digest-sigmoid`, `table-digest-rope`, `table-digest-exp` in both.
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
- `fp-host/tests/subproof_vectors.rs` replays the whole tool in Rust and matches the fixture.
- `fp-host/tests/subproof_tests.rs` runs the transcript-driven parts on a real `VerifierRounds`:
  the full `HTailF2::transcript` (RNG, commitment, the 31 tie sumchecks, 13 key levels, 11 table
  levels, the leaves and the bits) reaches the end with the planned slot count equal to
  `smallElems()`; `psc_begin`/`round_in`/`psc_ends`/`psc_row`, `stack_rounds`, `tsc_in`, `sc3_in`,
  `sc3_row` and `scd_in` all complete on hand-built plans. The chain itself is already replayed
  against C++ in `rounds_vectors.rs`.

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
- The frame side of `vf_subproof_segment.h` — `LinkCtx`, `currentSegment`, `rootInH`, `t2Batch`,
  `doorH`, `rowWeights`, `blk::ReqEquation` — is S3's wiring. `HTailF2::transcript` takes a
  [`SegmentGate`] for `fixedBeforeTheMatrixF` and `rootInH`; `OpenGate` is the test seam and is not
  the frame check.
- The C++ test harness's prover-value support (`HFork::valuesF`, `judged`, `judgeAll`, `take`,
  `valueOf`, `TestProverValues`) and the claim section names are omitted: no verifier decision
  reads them.
- `ShP::J` is 1 for every shape the programs make; `place_p` asserts it rather than defining the
  C++ division-by-zero case.
- `HForest` keeps the call metadata and returns each call's `alpha`/`zk`; the caller that owns the
  `Call`s writes them back (`HTailF2::transcript` does), because a Rust struct cannot point into
  its caller.

## 4. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve
rust-nostd-verifier/scripts/parity_subproof.sh
```

## 5. Still open for S3

The stage bodies (`run_stage`), the real-model `ShapesOf`, the frame/segment wiring
(`rootInH`/`t2Batch`/`doorH`), end-to-end `YES`/`result-v1` and the negative controls.
