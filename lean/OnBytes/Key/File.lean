-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/File.lean: the check of a whole key file.

A key file is, in this order (docs/format/FORMAT.md, R13.2):
  the head | the first table's root | the answers of its record | the one-time chain |
  the place | the shared chain | the second chain.
No part has a word for its own length. A byte that is left over is a refusal.

Root and answers are bytes of the file in front of the chains. The reader takes them first. They are
then, by value, in the statement of the one-time chain and of the shared chain, so a root that is
changed in the file changes every challenge.

How the file is checked. The public values are tested first. Then the file is read. The strict
reader reads the three chains under one record of tree vertices and makes the chains' hash calls.
The reading hashes two more things: the leaf of the binding tree (OnBytes/Proof/Place.lean) and, if
tables have a record, the chain that gives the record's seeds (OnBytes/Entry/Table.lean). Each
chain's description comes from a dry run of the chain's blocks. Then the decisions are taken on what
was read, chain by chain. What comes after the one-time chain has the same form in a proof file, and
is read and decided by OnBytes/Proof/Tail.lean.

The parameter bytes of the three chains are an argument, already read (`Params.KeyChains`).
`Key.check` does not ask where they come from, and its yes holds under the bytes that it was given.
Both callers derive them from public files: the stage "key" of `verify` and `verify -key`
(OnBytes/Model/VerifyStages.lean), and the call `key` on test files (OnBytes/Shell/Toys.lean).

What a yes says, on the protocol's analysis, which is not proved here: under the file's root lies a
table that is close to one code word and holds a matrix whose entries are in the ranges that the
parameter item "ranges" names. Nothing here judges whether these are the right ranges for a model. A
yes says nothing about whose weights these are: no item of a chain names a model, since no step
could check it. That a commitment belongs to a model of some name is its publisher's word.

What a yes does not tell. The C++ checker of a key file has three verdicts: no, yes, and yes with
its work counted. The last is for a key whose plans reach the public target only if the proofs of
work of their rounds are counted. It also reads no key under a plan that misses the target. Both
need the accounting of the rounds' errors, which `Key.check` does not make: it is its caller's
matter. So `Key.check` has two results. Its yes does not tell the two kinds of yes apart. And under
parameter bytes whose plans miss the target it can say yes where the C++ checker says no. Where the
parameter bytes are derived, a plan that misses the target is refused (`finishHeld`,
OnBytes/Params/Planner.lean). The stage "key" accounts for the work before it calls `Key.check`. The
call `key` on test files accounts for it after a yes (`keyWork`, OnBytes/Shell/Toys.lean); it ends
with the line `TEST FILES PASSED` and never with `YES`.

Main definitions: `Key.tailPublic`, `Key.readKey`, `Key.keyRefusal`, `Key.check`, `Key.names`.
C++ counterpart: check_key_under() and check_key() in blocks/frame/check_key.h.
-/
import OnBytes.Key.OneTime
import OnBytes.Key.Table

namespace OnBytes.Key

open OnBytes.Params (KeyChains TableName)
open OnBytes.Proof (Reading TailPublic TailRead need readNamed readTail judge tailRefusal)

/-- What is public about the part of a key file after its one-time chain. -/
def tailPublic (k : KeyChains) (table : TableName) : TailPublic :=
  ⟨k.shared, k.second, k.oneTime.binding, table, Params.labelShared, Params.labelSecond⟩

/-- Reads the three chains of a key file. j is the place of the first byte after the record's
answers. The names of the refusals say which part of the file was refused and, where the strict
reader refused, at which kind of check. -/
def readKey (k : KeyChains) (table : TableName) (file : ByteArray) (j : Nat) :
    Reading TailRead := do
  let p := k.oneTime
  let (rounds, dry) ← need "one-time-chain-parameters" ((oneTime p).dryRun (startOf p))
  let spec ← need "one-time-chain-parameters" (p.describe table rounds)
  let first ← readNamed "one-time-chain-" spec file j
  let r ← readTail (tailPublic k table) dry first file
  if r.next != file.size then throw "bytes-left-over"
  pure r

/-- The decision on the three views of a key file. Returns nothing for a yes, and else the name of
the chain that was refused, with the name of the test that failed first if that test has one. -/
def keyRefusal (k : KeyChains) (table : TableName) (r : TailRead) : Option String :=
  let p := k.oneTime
  match judge "one-time-chain-" (oneTime p) (startOf p) r.first.view with
  | .error why => some why
  | .ok real => tailRefusal (tailPublic k table) real r

/-- Checks the key file `file` under the parameter bytes of its three chains. Returns what a reader
keeps of the table, for every later entry and proof, or the first check that failed. A key file is
read under a record of tree vertices of its own. -/
def check (k : KeyChains) (file : ByteArray) : Except Refusal TableName :=
  let p := k.oneTime
  if p.given.plan.field != .two then .error ⟨.configuration, "key-field"⟩
  else if !admitted p then .error ⟨.configuration, "key-values"⟩
  else
    match readTable p.lin.fold.index p.given.cfg file with
    | .error e => .error e
    | .ok (table, j) =>
      match (readKey k table file j).fromStart with
      | .error why => no why
      | .ok r =>
        match keyRefusal k table r with
        | some why => no why
        | none => .ok table

/-- The names of refusals that this directory makes itself: those of the public values, of the
table's form, of the one-time chain, and of a byte that is left over. `Key.check` can also return
the names of the file's head, of the table's bytes, and of all that comes after the one-time chain
(its seal, the place, the table's record, the two later chains). They belong to the modules that
make them (OnBytes/Proof/Head.lean, OnBytes/Entry/Table.lean, OnBytes/Proof/Tail.lean). -/
def names : List String :=
  ["key-field", "key-values", "table-shape", "table", "one-time-chain-parameters",
   "bytes-left-over"] ++ Proof.namesOf "one-time-chain-"

end OnBytes.Key
