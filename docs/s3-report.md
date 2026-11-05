# S3 report: end-to-end YES and result-v1

S3 assembles the ported pieces into the reference program's whole call: the three stage bodies
(`runStage`), the frame-backed segment driver (`buildLinksH`/`runLinksH`), the real model's
`ShapesOf`, and the parent's assembly (`cpStagesRun`: stage headings and texts, the accounting
record, `covered:`, `id:`, `h_par=`, the work and commitment lines, `result-v1` and `YES`).

The accepted example now prints the reference's 105 lines byte for byte, with one normalization
allowed: the seconds in the three stage headings. Both negative controls print their goldens byte
for byte and exit 1.

## 1. What landed

| Module | C++ source | Content |
|---|---|---|
| `fp-core/src/verifier/run_stage.rs` | `cp_verify.cpp:1264-2538` | `run_stage`/`StageMode`/`StageFiles`/`StageOutcome`; the key, leaf and request stage bodies: setup (the strict policy scan, the layout, the statement), `configure`, the three file plans, the sub-proof plans and walks, the proof checks, the stage record and its last line. |
| `fp-core/src/verifier/stage_links.rs` | `vf_segments.inc:1-280` | the real model's `ShapesOf` and `buildLinksH`: `shapes_of`, `build_links`, the link metadata, and the identifiers/layout/range checks the shapes carry. |
| `fp-core/src/verifier/frame_segment.rs` | `vf_segments.inc:283-340`; `vf_subproof_segment.h` | `runLinksH`: `FrameSegment` (`first`/`later`/`close`/`finish`), the `rootInH`/`t2Batch`/`doorH` seam and the pending weight claims. |
| `fp-core/src/verifier/attention_run.rs`, `layers_check.rs`, `head_check.rs`, `smallness.rs`, `stage_layout.rs` | `vf_attention_check.h`, `vf_layers_check.inc`, `vf_output_head_check.inc`, `cp_verify.cpp` | the sub-proof walks wired to the real plans (the attention shape/plane fixes are part of this wiring). |
| `fp-host/src/main.rs` | `cp_verify.cpp:2560-3007, 3274-3389` | the whole call: `cpMain`'s reads and policy checks, `hParOf` (`configuration_digest`, 235 hash calls), `cpStagesRun` (headings and texts, status/record/work checks, `covered:`, `id:`/`h_par=`, the work, commitment and result lines, the YES/NO/NOT CHECKED/NOT-A-VERIFICATION endings), and `cpCovered`. |
| `scripts/parity_e2e.sh` | new | the S3 gate: the accepted example and the two negative controls. |

The call runs in one process: C++ forks one child per stage; the port runs key, leaf and request in
order, each on a fresh `StageState` (`fp-core/src/stage_state.rs`).

## 2. Evidence

### 2.1 The S3 gate

```sh
cd /Users/shakku/trustless-ai/FlashProve/rust-nostd-verifier
scripts/parity_e2e.sh
```

Full output:

```
PASS accepted example: 105 lines, exit 0, YES, result-v1 and q_V=136088, full stdout equal
PASS tampered proof: NO: proof-refused, exit 1, byte-equal to the golden
PASS wrong commitment ID: NO: model-statement, exit 1, byte-equal to the golden
parity_e2e: 3 passed, 0 failed
```

The accepted case compares the host's whole stdout with `fixtures/golden_stdout.txt` after one
normalization, the seconds in the three stage headings
(`---- stage <name> ---- N thread(s), X.XXX s`), and checks separately: exit status 0, empty
stderr, 105 lines, the `YES` line, the `result-v1` line byte for byte, and the q_V line with
136088.

The stage records' q_V and the call's:

- key: 28280; leaf: 12560; request: 95013 (sum 135853)
- the parent's own hash calls (`hParOf`'s configuration digest): 235
- the call's q_V: **136088**

The hard lines, byte for byte (`fixtures/golden_stdout.txt`, lines 70, 104 and 105):

```
accounting: hash calls: t, the prover's, is a free variable; q_V, the verifier's own in this run: 136088
result-v1 status=0 claim=exact-match id=79a5a2bc7a469b40df73dedf40abeb740671e8ae8077738bd3743897aeb22183 bits=128 work=32 work-rounds=38 least-round=128.00 least-round-without-work=96.23 commitment-assumed-rounds=49 record=1 r=60 e=64 T=64 tokens=61..63 y=yes policy=exact-match C=256 theta=256 cap=0 s=16 sh=8 sT=4 F=24 above-clip=0 leaf=0 stages=key,leaf,request dw=8 build=93afdaf592393a54ebd17b681d1c03295eb883f0161ff0e6ab872a3b39939595
YES
```

### 2.2 The negative controls

A tampered proof (byte 2072650 of `fixtures/example.proof`, XOR `0x01`), exit status 1, the whole
stdout:

```
---- the call ----
refused by the stage request: an opening does not lead to its root
NO: proof-refused
```

A wrong commitment ID (the last two hex digits `83` -> `84`), exit status 1, the whole stdout:

```
id: these are not the files of the commitment that you named; nothing in them was checked
id: take the commitment ID from your own record of where it was published, never from these files
NO: model-statement
```

Both are compared with `cmp`, not `diff`: these goldens are the whole stdout.

### 2.3 The earlier gates

```sh
scripts/parity.sh
```

```
...
PASS accepted example (C++ against golden_stdout.txt)
PASS tampered proof (C++ against golden_negative_tampered.txt)
PASS wrong commitment ID (C++ against golden_negative_wrong_id.txt)
PASS Rust host on the accepted example (against golden_stdout.txt)
parity: 31 passed, 0 failed
```

The C++ reference built by `parity.sh` from this checkout reproduces the stored goldens, including
`build=93afdaf5...` inside `result-v1`; the original C++ sources are unmodified. The `fp-core`
no_std scan finds no `use std`, `extern crate std` or `static mut`.

`cargo test --workspace`: **229 passed, 0 failed** in 56 test binaries, exit status 0.

## 3. Deviations and known gaps

- C++ forks one process per stage and may run the stages' sub-proofs on threads; the port runs the
  three stages in one process, in order, each on a fresh `StageState`. The only output difference
  is the stage headings' seconds, which the gate normalizes; everything else is byte-identical.
- A chain failure at `ChainCheck::first()`/`finish()` arrives as `LinkStop::False`, and
  `check_proof` prints the channel's reason as the proof's `NO` (`proof: ...`, `NO: proof-refused`),
  as the C++ does. The C++ `linkRefused()` paths that fire at a later commit point or at a
  segment's `close()` (which print `chain: <why>` and then `NO: chain-refused`) still travel as the
  port's internal carrier names; the S3 negative vectors do not reach them.
- The C++ test harness's prover-value support and section names remain omitted (S2c report).
- The `-key` and `-leaf` part calls are assembled by the same `cpStagesRun` port but are not part
  of the S3 gate.

## 4. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve/rust-nostd-verifier
scripts/parity_e2e.sh      # S3: accepted example and the two negative controls
scripts/parity.sh          # S1 CLI/input cases, the C++ goldens, and the accepted example
cargo test --workspace     # the whole workspace
```

## 5. Open for S4 and S5

The two negative controls of the S3 task book are gated here; S4 extends the negative set. S5 (the
zkVM guest) is gated on the S3 pass and on the PM's release.
