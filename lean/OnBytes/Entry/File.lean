-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/File.lean: the check of a whole entry file.

An entry file comes with a further stored copy of a key's table. It is, in order: the head; the
copy's root; the answers of the copy's record; the link's chain, with which the file ends
(docs/format/FORMAT.md, R13.3). The link is the protocol meant to tie the copy's rows to the
first table's (OnBytes/Iop/Link.lean). It is not a link of a request's proof (OnBytes/Iop/Req.lean).
A table's record is, for each row, the row's answers to a sample whose seeds follow from the table's
name (OnBytes/Iop/Foldeq.lean). Tables may have none.
Root and answers are bytes of the file before the chain. The reader takes them first and only then
starts the chain, whose statement holds both tables' roots and records by value. The first table is
never taken from the entry file: the caller passes it in, from a key file. The C++ counterpart is
check_entry_under (blocks/frame/check_entry.h).

Main definitions: `Entry.answersOf`, `Entry.read`, `Entry.check`, `Entry.names`,
`Entry.notes`.

What is not claimed. It is not tested that the first table has passed a key file's check: that is
the caller's duty. It is not tested that the parameter bytes follow from public files, or that the
plan in them reaches a target: a yes holds under the bytes that the caller passes in. Every call of
the program derives them from the public files and refuses a plan that does not hold its target, as
the C++ check does. It is not tested that plan and shape agree on how the positions of the round
`LINK` are divided between the two tables: the shape has the two numbers and the plan only their
sum, so the plan cannot tell them from the same two numbers swapped (OnBytes/Iop/Link.lean;
blocks/frame/check_entry.h, EntryUnder).
Beside yes and no, the C++ check_entry can answer a third way: yes, but only once the rounds' work
is credited. This program's yes does not tell those two kinds of yes apart.
-/
import OnBytes.Iop.Link
import OnBytes.Entry.Table
import OnBytes.Proof.Head
import OnBytes.Proof.Reading
import OnBytes.Result

namespace OnBytes.Entry

/-- A refusal in the stage of the entry file. -/
def no {α : Type} (check : String) : Except Refusal α := .error ⟨.entry, check⟩

/-- A refusal of the parameter bytes that the caller has passed in. -/
def noParameters {α : Type} : Except Refusal α := .error ⟨.configuration, "entry-parameters"⟩

/-- The field and the number of a record's answers, from the parameter bytes of the link's chain:
one answer for each row and seed. Returns nothing if the bytes are not those of a link. A reader of
the key file needs them to take the first table's root and answers. -/
def answersOf (params : ByteArray) : Option (Fmt.Fld × Nat) :=
  (Params.Link.read params).map fun p =>
    (p.given.plan.field, p.link.table.rows * p.link.table.answers)

/-- A link's block starts from the plan's rounds and answers to a sample, the codes, and no tree. -/
def start (p : Params.Link) : Start :=
  { entries := p.given.rounds, samples := p.given.plan.samples, st := { codes := p.codes } }

/-- An entry file as it was read, before any decision: the copy, the block of its chain, and the
chain. -/
structure EntryRead where
  further : Params.TableName
  block : Blk Unit
  chain : ChainRead

/-- Reads the entry file `file` under the parameter bytes of the link's chain, against the first
table. The chain's decision is left to `check`; until then the copy counts as unchecked. The check
of an entry file is one verdict: it keeps its own list of the tree vertices that it has met
(FORMAT.md, R7.14; OnBytes/Chain/Session.lean). Parameter bytes for a field other than the one in
which this program computes, or with 32 zero bytes as the digest of the public files, are refused.
-/
def read (p : Params.Link) (first : Params.TableName) (file : ByteArray) :
    Except Refusal EntryRead :=
  let f := p.given.plan.field
  let shape := p.link.table
  match Proof.readHead f .entry file with
  | .error e => no e
  | .ok i =>
    if f != .two || p.given.cfg == Fmt.zero32 then noParameters else
    match readTable f (shape.rows * shape.answers) file i with
    | .error e => no e
    | .ok (further, j) =>
      match tableKey f p.given.cfg shape first 0, tableKey f p.given.cfg shape further 1 with
      | some k0, some k1 =>
        let block := linkVerify p.link k0 k1
        match (block.rounds (start p)).bind (p.describe first further) with
        | none => noParameters
        | some spec =>
          match (Proof.readNamed "" spec file j).fromStart with
          | .error e => no e
          | .ok r => if r.next != file.size then no "bytes-left-over" else .ok ⟨further, block, r⟩
      | _, _ => no "table-record"

/-- Checks the entry file `file` under the parameter bytes `params` of the link's chain, against the
first table. Returns what a reader keeps of the copy, or the first check that failed. -/
def check (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    Except Refusal Params.TableName :=
  match Params.Link.read params with
  | none => noParameters
  | some p =>
    match read p first file with
    | .error e => .error e
    | .ok r =>
      match Proof.judge "" r.block (start p) r.chain.view with
      | .ok () => .ok r.further
      | .error why => no why

/-- The names under which the checks of this file refuse. -/
def names : List String :=
  ["entry-parameters", "bytes-left-over", "table-record"] ++ Proof.headNames ++ tableNames ++
    Proof.namesOf ""

/-- The intermediate values that the link's block notes in its run on the view, in their order. No
test reads them. They let this verifier be compared with another one, value by value. -/
def notes (p : Params.Link) (r : EntryRead) : Array (String × E) :=
  r.block.notesOn (start p) r.chain.view

end OnBytes.Entry
