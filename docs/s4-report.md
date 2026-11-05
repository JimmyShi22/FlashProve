# S4 report: the negative controls

S4 widens the gate beyond the two S3 controls. It plays the cases of the two reference tests —
`verifier/tests/commitment_id_test.py` and `verifier/tests/what_a_yes_covers_test.py` — and adds
mutations of every input file class: the key, the leaf file, the proof's header and body, the
parameter file's policy numbers, `KL.bin`'s length, and the request and y files.

Every case runs the C++ reference (`cp_verify`) and the Rust host (`fp-host`) with the same
arguments and compares stdout (with only the stage headings' seconds normalized), stderr and the
exit status byte for byte. The script also checks each case's expected exit status and last line,
and records the rejection names it reached.

## 1. What landed

| Module | C++ source | Content |
|---|---|---|
| `fp-core/src/verifier/run_stage.rs` | `cp_verify.cpp:2255-2268, 2435-2461, 3124-3159` | `StageMode::PlanId` (`-plan id`): `h_par=`, the `commitment ID:` line, `PLAN ONLY`, status 4. `StageFiles::plan_only` (`-plan accounting`): the request stage stops after the plans, prints `planEndH` and ends at 4. A planning call keeps the request's sub-proofs (`Setup::sub`); a checking call does not. |
| `fp-core/src/frame/prints.rs` | `blocks/frame/prints.h` | `print_test`, `print_size`, `print_plan` (`-plan accounting`'s 94-line output). The round and field listings (`print_rounds`, `print_fields`) are not ported: no S4 case asks for them. |
| `fp-core/src/numbers/real.rs` | `real.h:232-245` | `Big::dec()`, the decimal digits that `print_test` prints as `list ..`. |
| `fp-core/src/frame/files.rs`, `frame_segment.rs`, `stage_links.rs` | `files.h`, `vf_segments.inc`, `vf_output_head_check.inc:36` | the sub-proof planners are `Rc` so a planning call can keep the sub-proofs; and a bug fix: the head sub-proof now checks the token at position `T - 1` that the proof itself sent, not the caller's y (see §3). |
| `fp-host/src/main.rs` | `cp_verify.cpp:3120-3218` | `-plan id` and `-plan accounting` run the stage and print its output; `-plan arrays` and `-plan request` stay NOT CHECKED. |
| `scripts/parity_negative.sh` | new | the S4 gate: 70 cases, the expected ending of each, and the rejection-name checklist. |
| `fixtures/negative/` | new | `README.md` (the mutation recipes) and `record.tsv` (one line per case: name, exit status, last stdout line, arguments). |

## 2. Evidence

```sh
cd /Users/shakku/trustless-ai/FlashProve/rust-nostd-verifier
scripts/parity_negative.sh
```

Final lines of the run:

```
PASS proof_tag: exit 1, NO: cp-proof-head
PASS proof_version: exit 1, NO: cp-proof-head
PASS proof_middle: exit 1, NO: proof-refused
PASS kl_short: exit 1, NO: KL-length
PASS kl_odd: exit 1, NO: KL-length
parity_negative: rejection names reached:
     2 KL-length
     1 cp-key-head
     2 cp-proof-head
     2 entry-refused
     1 key-refused
     5 model-statement
    11 policy
     4 proof-refused
     2 reply-differs
     6 statement-range
     3 statement-required
parity_negative: rejection names on the checklist: 11/11
parity_negative: 70 passed, 0 failed
```

`cargo test --workspace`: **229 passed, 0 failed**. `scripts/parity_e2e.sh` (S3): **3 passed, 0
failed**. `scripts/parity.sh` (S1): **31 passed, 0 failed**. The `fp-core` no_std scan is clean.
`fixtures/negative/record.tsv` holds the exit status and last line of every case (see §5).

## 3. The two reference tests, assertion by assertion

### `commitment_id_test.py`

The test forms the commitment ID (and the shorter ID without the seeds' list and the closing word
0) with `docs/format/format_rules.py`, then runs three calls. `scripts/parity_negative.sh` forms
the two IDs the same way and asserts that the ID is the one in `fixtures/ID.txt`.

| Assertion | S4 case | Result |
|---|---|---|
| `-plan id` prints the ID, status 4 | `plan_id` | PASS, byte-equal |
| `-key .. -id <ID>`: status 3, `PART PASSED ..` | `key_named` | PASS, byte-equal |
| `-key .. -id <shorter ID>`: status 1, `NO: model-statement` | `key_shorter` | PASS, byte-equal |

### `what_a_yes_covers_test.py`

The test's world is synthetic and written by the GPU prover
(`verifier/tests/other_parameters_worlds.sh`). S4 plays its cases on this repository's real-model
fixtures: the same case classes, the same options, and the same expected endings, with the exact
request the fixtures carry (positions 60 to 63 of 64, so the proof covers four tokens and the
answer). The test's optional `in-two/`/`in-one/` proofs are not played — the test itself reports
"in part" without them.

| Assertion (test) | S4 case(s) | Result |
|---|---|---|
| the honest call ends YES (0), one `covered:` line, the four closing lines, three stage headings | `honest` | PASS, byte-equal (only stage seconds normalized) |
| the same with `-q` | `honest` (every stage case already passes `-q`) | covered |
| without `-id`: 14, condition `id-named`; also with `-show-stages` | `without_id`, `without_id_show` | PASS |
| under another ID: NO, and the files' ID appears nowhere | `other_id` | PASS (`NO: model-statement`) |
| `-policy` with the file's own numbers: as without it | `policy_own` | PASS (YES) |
| `-policy` clipped-gap: two lines, `policy:` then `NO: policy` | `policy_clipped` | PASS |
| `-policy` log-probability: status 2, nothing on stdout | `policy_logprob` | PASS |
| each of C, theta, cap, s, sh greater by one: `NO: policy` | `policy_c_plus`, `policy_theta_plus`, `policy_cap_plus`, `policy_s_plus`, `policy_sh_plus` | PASS |
| `-next-token`: as without it if `r = T - 1, e = T`; otherwise 14 with condition `next-token` | `next_token`, `next_token_no_id` | PASS (the fixtures' request covers four tokens, so this is the test's other branch: 14, from both the C++ reference and the port) |
| `-no-proof-of-work` where `policy.txt` declares counted work: 14, condition `no-proof-of-work`; also with `-show-stages`, twice, with `-next-token`, and with no `-id` (both conditions) | `no_work`, `no_work_show`, `no_work_twice`, `no_work_next`, `no_work_no_id` | PASS |
| `-no-proof-of-work` under another ID: NO | `no_work_other_id` | PASS |
| `-no-proof-of-work` and another y, or a proof with one bit turned: NO | `no_work_other_y`, `no_work_turned` | PASS |
| a wider stretch (`r = T - 2`), a prompt token turned, another y: NO | `wider`, `prompt_turned`, `other_y` | PASS |
| a parameter file that sets another policy than the exact match: `NO: policy` without `-policy`; a policy that bars no token, rightly named: `NO: policy`; the same rightly named or y-alone: another NO | `gap_no_policy`, `gap_named`, `gap_y_only`, `loose_named`, `loose_y_only` | PASS |
| the file sets the kind log-probability or another-table (`sT`): `NO: policy` | `kind_logprob`, `kind_another` | PASS |
| the request one word shorter or longer, a y of two words: `NO: statement-range` | `req_shorter`, `req_longer`, `y_two_words` | PASS |
| the request one byte longer, empty; an empty y: `NO: statement-required` | `req_odd`, `req_empty`, `y_empty` | PASS |
| the shorter request under another ID, with another policy, without a proof file: `NO: statement-range` | `req_shorter_other_id`, `req_shorter_other_policy`, `req_shorter_no_proof` | PASS |
| an input missing or not a regular file: one `input-unreadable-<role>` line, status 2 | `no_policy`, `no_kl`, `layout_is_a_folder`, `no_key`, `no_request`, `no_y`, `no_proof`, `proof_is_a_folder`, `key_no_key`, `leaf_no_entry`, `plan_id_no_key` | PASS |
| `-key` and `-leaf` on the honest files: status 3, `PART PASSED`, the work line | `part_key`, `part_leaf` | PASS |
| `-plan accounting`: status 4, ending `PLAN ONLY: ..`; with `-no-proof-of-work`: status 2, nothing on stdout | `plan_accounting`, `plan_accounting_option` | PASS |
| `-key`/`-leaf` with `-no-proof-of-work`: 14, no stage output | `part_key_no_work`, `part_leaf_no_work` | PASS |

## 4. The S4 mutations

All are deterministic recipes over the stored fixtures (`fixtures/negative/README.md` records
them).

| Family | Cases | Endings |
|---|---|---|
| key.bin, header word | `key_header` | `NO: cp-key-head` |
| key.bin, middle byte | `key_middle` | `NO: key-refused` |
| leaf file, header word | `leaf_header` | `NO: entry-refused` |
| leaf file, middle byte | `leaf_middle` | `NO: entry-refused` |
| proof header, tag `CPPF` | `proof_tag` | `NO: cp-proof-head` |
| proof header, version word | `proof_version` | `NO: cp-proof-head` |
| proof body, middle byte | `proof_middle` | `NO: proof-refused` |
| `KL.bin` shorter than the digest's 8 words | `kl_short` | `NO: KL-length` |
| `KL.bin` whose length is no multiple of 4 | `kl_odd` | `NO: KL-length` |
| `policy.txt`: C, theta, cap, sT | `config-gap`, `config-loose`, `config-logprob`, `config-another` cases | `NO: policy`, `NO: model-statement` |
| request: r/e, tokens, length, empty | `req_*`, `wider`, `prompt_turned` | `NO: statement-range`, `NO: statement-required`, `NO: proof-refused` |
| y: another token, length, empty | `other_y`, `y_two_words`, `y_empty` | `NO: reply-differs`, `NO: statement-range`, `NO: statement-required` |

## 5. The rejection-name checklist

The two reference tests assert `model-statement`, `policy`, `statement-range` and
`statement-required`; the S4 mutations add the rejections of the corrupted files. The script
requires each name below to appear at least once among the cases' `NO:` lines and fails the gate
otherwise (11/11):

| Name | Reached by |
|---|---|
| `model-statement` | `key_shorter`, `other_id`, `gap_named`, `loose_y_only`, `no_work_other_id` |
| `policy` | the `policy_*`, `gap_*`, `loose_*` and `kind_*` families (11 cases) |
| `statement-range` | `req_shorter`, `req_longer`, `y_two_words`, `req_shorter_other_id`, `req_shorter_other_policy`, `req_shorter_no_proof` |
| `statement-required` | `req_odd`, `req_empty`, `y_empty` |
| `proof-refused` | `proof_middle`, `no_work_turned`, `wider`, `prompt_turned` |
| `reply-differs` | `other_y`, `no_work_other_y` |
| `key-refused` | `key_middle` |
| `entry-refused` | `leaf_header`, `leaf_middle` |
| `cp-key-head` | `key_header` |
| `cp-proof-head` | `proof_tag`, `proof_version` |
| `KL-length` | `kl_short`, `kl_odd` |

The `input-unreadable-<role>` lines are not rejection names; the 11 unreadable cases check the
line's role and text instead.

## 6. A bug found by S4

The output-head sub-proof checked the token at position `T - 1` from the caller's y, but the C++
takes the reply that the proof itself sent (`vf_output_head_check.inc:36`: `if (hOn[T - 1]) win[T
- 1] = yTok;`) and lets `check_proof` compare the two after the links. With another y the port
therefore refused inside the BASE check (`NO: proof-refused`) where the reference ends `NO:
reply-differs`. `frame_segment.rs` now builds the head's window with the proof's reply; `other_y`
and `no_work_other_y` are byte-equal to the reference.

## 7. Deviations and known gaps

- The C++ prints verbose stage lines, some with wall-clock seconds, without `-q`; the port does
  not print them. Every S4 case that runs a stage therefore passes `-q` (the S3 golden's mode) to
  both programs. Cases that print before any stage (usage errors, `-policy` rejections, unreadable
  inputs, the statement length checks and the `-plan` calls) run unchanged.
- The `what_a_yes_covers_test.py` world is synthetic and made with the GPU prover, so S4 plays
  its case classes on the real-model fixtures. The optional two-token/one-token proofs are not
  played, as the test itself allows ("in part").
- `-plan arrays` and `-plan request` still end NOT CHECKED; neither reference test uses them.

## 8. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve/rust-nostd-verifier
scripts/parity_negative.sh   # S4: 70 cases and the rejection-name checklist
scripts/parity_e2e.sh        # S3: the accepted example and the two S3 controls
scripts/parity.sh            # S1: the CLI/input cases and the C++ goldens
cargo test --workspace
```
