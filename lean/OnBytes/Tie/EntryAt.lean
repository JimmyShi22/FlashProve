-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAt.lean: the chain's reader of an entry file at any function O on byte strings in
the place of the hash, and the program's reader as its case at the format's hash.


OnBytes/Tie/EntryWithRec.lean writes `Entry.check` a second time with the chain's reader as a
parameter. OnBytes/Tie/StoredAt.lean and OnBytes/Tie/DigestPoint.lean give a reader for every
function O on byte strings: the library's strict reader at the hash that O induces, with one string,
that of the digest of the parameter bytes, answered by the format's own digest. This file names that
reader; OnBytes/Tie/EntryAtRec.lean puts it in.

Main definition: `readerAt`.
Main theorems.
- `withinX_statement`: a description within `withinX` that is in order has a statement of fewer than
  2^64 bytes.







- `readerAt_oracle`: within `smallFX`, the reader at the format's own oracle is the program's reader
  `readIn`.






What is not claimed. Nothing on soundness, and no probability: O is a fixed function in every
statement, nothing is drawn, and no queries are counted. `readerAt O` is a function of O. It is no
computation that asks an oracle, and the type of `rd` in `checkWithR` admits no reader that asks.
None is in this file.

Of a yes of the compiled verifier at O nothing is proved here. `readerAt` is no part
of the program, which does not import this file, runs `Entry.check` and calls the format's hash. By
its text, whatever O is, `readerAt O` computes at most one value with the format's hash, the digest
of the parameter bytes of the description (`pinned`); that is no theorem. Of `checkAtR`, which puts
it in: that these are the bytes `params` that it was given is not stated here
(`Slice.entrySpec_params`, OnBytes/Slice/NamesAt.lean). The 32 bytes in `params` that stand for the
digest of the public files are taken as they are: nothing here makes them a digest.
`checkAtR` does not test the length of the first table's root, which the caller hands in:
`entry_check_atR` and `entry_closedR` take a first root of 32 bytes as a hypothesis.
That some file makes `checkAtR O` say yes is not stated, for any
O. All limits in the heads of OnBytes/Tie/StoredAt.lean and OnBytes/Tie/DigestPoint.lean hold here
too. The program is the Lean port built from OnBytes/; nothing here is said of the C++ program
`cp_verify` or of how its results compare. For proofs only; the program does not import this file.

-/
import OnBytes.Tie.EntryWith
import OnBytes.Tie.EntryPre
import OnBytes.Tie.SpecXBase
import OnBytes.Tie.DigestPoint

set_option autoImplicit false

namespace OnBytes.Tie

/-- The chain's reader at O: the library's strict reader at the hash that O induces, but for the one
string of the digest of the description's parameter bytes, which is answered by the format's own
digest (`pinned`). The program does not call it. -/
def readerAt (O : ByteArray → ByteArray) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    InSession ChainRead :=
  readInAt (pinned O S.base.params) S b i

/-- A description within `withinX` that is in order has a statement of fewer than 2^64 bytes. -/
theorem withinX_statement (S : Fmt.SpecX) (hok : S.ok = true) (hw : withinX S = true) :
    S.base.statement.size < 2 ^ 64 := by
  have hsm := smallFX_of_withinX S hok hw ByteArray.empty (by decide)
  unfold smallFX Run.smallF Run.smallB at hsm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm
  have := hsm.1.1.1.1.1.2
  omega

/-- Within `smallFX` the reader at the format's own oracle is the program's reader. -/
theorem readerAt_oracle (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session)
    (hsm : smallFX S b = true) : readerAt Fmt.oracle S b i s = readIn S b i s :=
  readInPinned_oracle S b i s hsm

end OnBytes.Tie
