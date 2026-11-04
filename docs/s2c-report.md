# S2c report: the verifier's sub-proofs

S2c comes in two waves:

- **S2c-1** — the shared foundation: the public table gate, `vf_common` core, the transcript
  channel, the sub-proof engine, smallness/packing/test, the lookup argument/helpers and the
  sumcheck variants.
- **S2c-2** — the three sub-proofs (attention, layers, output head) and the join.

## 1. What landed

| Module | C++ source | Content |
|---|---|---|
| `verifier/tables.rs` | `cp_verify.cpp:181-215,1301-1303,1412-1428,1592-1610,2004-2011`; `vf_attention_shape.h:203-212` | `TableParams` (`eg`, `smax`, `gcl`, `theta0`, `cs`, `dh`, `lt`, `S`, `rx`), `sigmoid_table_entry`, `sigmoid_clamp_table_entry`, `gate_table_entry`, `silu_table`, `sigmoid_table`, `rope_table`, `exp_table`, `table_digest` (H(72; ·)), `check_table_digests` |


## 2. Evidence

- `scripts/parity_subproof.sh`: **8 passed, 0 failed** — the two C++ tool/fixture comparisons, the
  three Rust replays (common, transcript, tables), the workspace build/test and the no_std scan.
- `table_vectors`: the C++ tool includes `cp_verify.cpp` as a translation unit and calls the actual
  static table functions and `earlier_hash_h_digest`; it dumps all 65,536 SILU entries, 65,536 SIG
  entries (the accepted model has `NE = 4`), 8,192 RoPE entries and 2,307 softmax entries, their
  H(72; ·) digests, the policy's 32 digest words and the accept/reject results. The Rust replay
  matches every integer entry and digest; the accepted policy's `tsilu*`/`tsig*`/`trope*`/`texp*`
  lines match, and flipping one word of each expected digest yields `table-digest-silu`,
  `table-digest-sigmoid`, `table-digest-rope`, `table-digest-exp` in both.
- Integer rounding is exact: the library's `exp`/`sin`/`cos`/`pow` may differ from the platform by
  one ULP, but every entry is compared as an integer, and the 32 digest lines are the format's own
  ground truth.


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


## 4. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve
rust-nostd-verifier/scripts/parity_subproof.sh
```

## 5. Still open for S3

The stage bodies (`run_stage`), the real-model `ShapesOf`, end-to-end `YES`/`result-v1` and the
negative controls.
