-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/File.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Entry/File.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Entry.File
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Proof.Reading

namespace OnBytes.TwoPort.M.Entry

open OnBytes.Entry

/-- Reads the entry file `file` under the parameter bytes of the link's chain, against the first
table. The chain's decision is left to `check`; until then the copy counts as unchecked. The check
of an entry file is one verdict: it keeps its own list of the tree vertices that it has met
(FORMAT.md, R7.14; OnBytes/Chain/Session.lean). Parameter bytes for a field other than the one in
which this program computes, or with 32 zero bytes as the digest of the public files, are refused.
-/
def read {m : Type → Type} [Monad m] (hh : HashM m) (p : Params.Link) (first : Params.TableName)
    (file : ByteArray) : m (Except Refusal EntryRead) :=
  let f := p.given.plan.field
  let shape := p.link.table
  match Proof.readHead f .entry file with
  | .error e => pure (no e)
  | .ok i =>
    if f != .two || p.given.cfg == Fmt.zero32 then pure noParameters else
    match readTable f (shape.rows * shape.answers) file i with
    | .error e => pure (no e)
    | .ok (further, j) => do
      let a0 ← tableKey hh f p.given.cfg shape first 0
      let a1 ← tableKey hh f p.given.cfg shape further 1
      match a0, a1 with
      | some k0, some k1 =>
        let block := linkVerify p.link k0 k1
        match (block.rounds (start p)).bind (p.describe first further) with
        | none => pure noParameters
        | some spec =>
          match ← (Proof.readNamed hh "" spec file j).fromStart with
          | .error e => pure (no e)
          | .ok r =>
            pure (if r.next != file.size then no "bytes-left-over" else .ok ⟨further, block, r⟩)
      | _, _ => pure (no "table-record")

/-- Checks the entry file `file` under the parameter bytes `params` of the link's chain, against the
first table. Returns what a reader keeps of the copy, or the first check that failed. -/
def check {m : Type → Type} [Monad m] (hh : HashM m) (params : ByteArray) (first : Params.TableName)
    (file : ByteArray) : m (Except Refusal Params.TableName) :=
  match Params.Link.read params with
  | none => pure noParameters
  | some p => do
    match ← read hh p first file with
    | .error e => pure (.error e)
    | .ok r =>
      match Proof.judge "" r.block (start p) r.chain.view with
      | .ok () => pure (.ok r.further)
      | .error why => pure (no why)

end OnBytes.TwoPort.M.Entry
