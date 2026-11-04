# S2b-1 report: the verifier's foundation

S2b-1 ports the modules under everything else — the message codec, the hash chain and its
channel, the Merkle tree and its openings, and the Reed–Solomon code — with independent C++
vector tools and byte-for-byte parity. It stops before the proof-system blocks (S2b-2..4).

## 1. What was ported

| Port file | C++ source | Notes |
|---|---|---|
| `fp-core/src/iop/message.rs` | `blocks/iop/message.h` | `Writer`, `Reader`, item list, marks, `append_writer` |
| `fp-core/src/chain/chain.rs` | `blocks/chain/chain.h` | `FirstQuery`, `Chain`, round kinds, draws, work test |
| `fp-core/src/chain/public.rs` | `blocks/chain/public.h` | `Public<T>`, `Binder`, `Sealed`, `ChainFate`, `PublicBytes` |
| `fp-core/src/chain/session.rs` | `blocks/chain/session.h` | tree records per root, chain fates, `accepted()` |
| `fp-core/src/chain/rounds.rs` | `blocks/chain/rounds.h` (verifier side) | `VerifierRounds`, four draw handles, `SentRoot`, `record_seeds` |
| `fp-core/src/tree/tree.rs` | `blocks/tree/tree.h` | `TreeShape`, `TreeValues`, `TreeSide`, `tree_walk`, `tree_check` |
| `fp-core/src/tree/positions.rs` | `blocks/tree/positions.h` | `PositionList` |
| `fp-core/src/tree/opening.rs` | `blocks/tree/opening.h` (verifier side) | `OracleTreeShape`, `LeafHash`, `Opening`, read/write/check, `receive_opening` |
| `fp-core/src/code/code.rs` | `blocks/code/code.h` | `Code`, factors, generator rows, `symbol_at`, `Encoder` |
| `fp-core/src/code/cosets.rs` | `blocks/code/cosets.h` | points, factors, transform table (built explicitly, no mutex/global cache) |
| `fp-core/src/code/short_position.rs` | `blocks/code/short_position.h` | `short_position` |
| `fp-core/src/numbers/plan.rs` (addition) | `blocks/numbers/plan.h` | `Cursor` |

`lib.rs` now declares `chain`, `code`, `iop` and `tree`; `tree/mod.rs` exports `opening`. The
core still allocates only through `alloc`; `HashCalls` remains an explicit parameter and there is
no file-scope mutable static.

## 2. C++ vectors and parity

Four new tools include the checkout's own headers and dump values that the Rust tests replay.
They are not derived from the Rust code.

| Tool | Fixture | Content |
|---|---|---|
| `scripts/cpp_vectors/message_vectors.cpp` | `fixtures/message_vectors.txt` | bytes of typed items, the item list and marks, an appended writer, reader failures (cut, non-canonical F/E, leftovers) |
| `scripts/cpp_vectors/chain_vectors.cpp` | `fixtures/chain_vectors.txt` | three first queries (salted/unsalted, small/high labels, long statements), 12 rounds of all kinds, one round with 4 work bits, every draw, the fast path (`draw_E_straight`), record seeds, and the C++ `blk` hash-call count after every step |
| `scripts/cpp_vectors/tree_code_vectors.cpp` | `fixtures/tree_code_vectors.txt` | three tree shapes with leaves, openings at three lists, opening bytes, `TreeValues` across two lists, a tampered opening, three codes' points/factors/generator rows/symbols over F and E, `Encoder` encode/decode and transform tables, short positions |
| `scripts/cpp_vectors/rounds_vectors.cpp` | `fixtures/rounds_vectors.txt` | a hand-built plan (8 rounds, all kinds, a 2-bit work round), the Binder's parameter/statement bytes and digest, a proof made by C++ `ProverRounds`, and its acceptance by C++ `VerifierRounds` |

`scripts/parity_base.sh` rebuilds all four tools, diffs their output against the fixtures, runs
the four Rust tests, builds and tests the whole workspace, and scans `fp-core/src` for
`use std`, `extern crate std` and `static mut`.

Evidence (2026-11-05):

```
parity_base: 11 passed, 0 failed
parity_field: PASS   (S2a lane A, unchanged)
parity_hash: PASS    (S2a lane B, unchanged)
parity_numbers: PASS (S2a lane C, unchanged)
parity.sh: 25 passed, 0 failed (S1 gate, unchanged)
cargo test --workspace: 29 tests, 0 failed
```

The chain vectors compare `HashCalls::blk` with the C++ count for every operation, including the
fast path's saved call. The work round's fixture count excludes the prover's nonce search, which
a verifier never makes.

## 3. Rust tests added

- `fp-host/tests/message_vectors.rs` — writer bytes/items/marks, appended writer, reader values and
  failures.
- `fp-host/tests/chain_vectors.rs` — replays every first query, round, draw, trit matrix, seal and
  record seed, and checks the hash-call count after each line.
- `fp-host/tests/tree_code_vectors.rs` — leaves, openings, round trip, `TreeValues`/clash/tamper,
  code points/generator rows/symbols, `Encoder` over F and E, transform table, short positions.
- `fp-host/tests/rounds_vectors.rs` — Binder bytes and digest parity, then reads the C++ proof
  through `VerifierRounds` and compares every draw, seed, trit, position and the seal. A second
  test rejects cut, half, overlong and empty proofs.

## 4. A bug the foundation vectors caught

`run_value()` in `hash/modes.rs` built its tag as `Tag::plain(Domain::Run, label)`, putting the
label in the tag's tree field. C++ hashes `node(Domain::RUN, label, ..)`: the tag holds tree 0 and
the label is the index. S2a's hash vectors did not cover `run_value`, so the error survived until
the chain vectors used labels above `2^16`. The fix is one line; all S2a gates still pass.

## 5. Deliberate differences from the C++ shape

- A `VerifierRounds` holds `&mut VerifierSession`. Rust can therefore call `accepted()` only after
  every channel of the session has been dropped; each channel's `Drop` records a rejection in its
  shared `ChainFate`. C++ additionally asks a live channel's `ok()` through a closure
  (`still_good`); the borrow makes that question unrepresentable here, and the verdict at drop is
  the same one, since `accepted()` runs after the scope.
- Diagnostics that C++ prints to stderr before a fatal guard are part of the Rust panic message;
  there is no stderr in a `no_std` core.
- `tree_walk`'s `Side` is a Rust trait (`leaf`, `given -> Option<Value>`, `node`) rather than C++'s
  out-parameter protocol. The walk order and the chosen digests are unchanged, and the vectors
  prove it through the opening bytes and `given` counts.
- `gl64_table` is returned to the caller; there is no mutex-protected cache or process-wide table.
- The prover's `OracleTree`, `ProverRounds`, `Lent`/`take_back` and the test-only
  `messages_stay_outside` switch are not ported; S2b-1 is the verifier's side.

## 6. Reproduce

```sh
cd /Users/shakku/trustless-ai/FlashProve
rust-nostd-verifier/scripts/parity_base.sh
rust-nostd-verifier/scripts/parity_field.sh
rust-nostd-verifier/scripts/parity_hash.sh
rust-nostd-verifier/scripts/parity_numbers.sh
rust-nostd-verifier/scripts/parity.sh
```

## 7. Still open

S2b-2 (relation, tensor, hp, psc, summand, mask, line, bat, batt, split, fold, cs, laid,
single_rows, iopp, base_case), S2b-3 (foldeq, lin, link, member, lkp, rng, wf), and S2b-4
(frame, parameters, derive, configure, files, heads, hiding_conditions, and the S1 deferred items:
the `-plan` stub, `cpPolicyHeld`, strict `pol_word_u64`). The plan builders of
`blocks/numbers/blocks.h` still need their subset for S3; S2b-1 tests build plans by hand or from
the dumped fields.
