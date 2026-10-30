-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToyClauses.lean: the tests of form on a declared structure, clause by
clause, at the toy of OnBytes/Entry/RecordToyFiles.lean (OnBytes/Entry/TestRecordToyDeclared.lean).

Declared.entryFormOk (Fmt/Parsed.lean) is a conjunction. Six of its clauses are functions with a
name: Declared.settingOk, Declared.chainOk, ChainDecl.takenOk, SpecX.ok of the description,
storedShapeOk, entryShapeOk. `clauses` evaluates these six, in this order, and then the whole. So a
test here says not only that a changed structure is refused, but which named clauses refuse it.
Where all six pass and the whole says no, one of the clauses without a name has refused.

1. Two hands on the description. The declared chain's label and first tree's number, and its rounds'
   entries, stored trees and openings, were read off the description that Entry.read makes, so on
   these nothing is tried. What is tried: each
   round's kind, which Declared.spec takes from the round's name (kindOf), and the cut of each
   round's message into items, which it takes from three words of the entry (Entry.cut), are those
   under which Entry.check has read the programs' file; so are the parameter bytes, the statement,
   the digest of the public files and the case of the random bytes.
2. Entry.cut at made-up entries: answers first, then roots, then elements of 24 bytes. A number of
   bytes that no cut has is refused by Declared.chainOk.
3. The digest. Declared.entryFormOkOwn says yes. In Declared.entryFormOk the digest is a free
   argument: 32 zero bytes pass. That is a limit of the test, held here by an evaluation.
4. The tables' shape, told twice. Each of its six words changed alone is refused; which clause sees
   which word is held. With the stored trees' depth changed in the rounds and the shape kept,
   storedShapeOk alone refuses. The setting's salt is compared with no word of the shape: 48 passes
   every clause; at 39, a length that no leaf's salt has (R7.3), SpecX.ok alone refuses.
5. A round under a name that the format has not; each round that samples positions, made to open
   nothing; a tree taken over; a round SEAL at the end.
6. The random bytes as an item of the statement: Declared.spec takes the item's 32 bytes; where the
   statement has no such item it gives nothing.
7. The statement's form (EntryStm.ok): a root of 31 bytes, an answer too few, and an answer whose
   first word is the field's modulus p, which spells no element (R1.3, R1.4), are refused, in the
   first table and in the further one. With p - 1 in that place the form is in order.

What is expected follows from the text of the clauses and the rules that they name (R4.5, R7.3,
R7.4, R7.13, R8.7, R13.5, R13.8 to R13.12, R14.11: docs/format/). The places of the rounds that
sample positions were read off the entries in the programs' parameter bytes by a program outside
Lean. No expected value was read off an evaluation in Lean.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. The changed structures are made up: no public files give them. That the
random bytes stand in the file is refused by itself in no test. Nor is ChainDecl.takenOk: the link
has no chain in front of it, so Declared.spec gives nothing for a tree that is taken over, and the
clause on the description refuses too. Nothing on soundness, completeness
or hiding.
-/
import OnBytes.Entry.TestRecordToyDeclared

namespace OnBytes.Entry.RecordToy
open Fmt

/-- The structure with round i of the link, from 0, changed by g. -/
def roundChanged (D : Declared) (i : Nat) (g : DeclaredRound → DeclaredRound) : Declared :=
  let rounds := D.link.rounds.zipIdx.map fun r => if r.2 == i then g r.1 else r.1
  { D with link := { D.link with rounds := rounds } }

/-- The six clauses of Declared.entryFormOk that have a name, in its order, and then the whole. -/
def clauses (D : Declared) (cfg : ByteArray) (x : EntryStm) : List Bool :=
  [D.settingOk, D.chainOk D.link, D.link.takenOk [],
    (D.spec D.link cfg x.bytes).any fun S => S.ok, storedShapeOk D.table D.link, entryShapeOk D,
    D.entryFormOk cfg x]

/-- `clauses` at the toy's structure changed by g, under the toy's digest and statement. -/
def clausesAt (g : Declared → Declared) : Option (List Bool) :=
  declared.bind fun D => statementAt.map fun x => clauses (g D) D.cfg x

/-- The places, from 0, of the link's rounds that sample positions. -/
def samplingRounds (D : Declared) : List Nat :=
  (D.link.rounds.zipIdx.filter fun r => r.1.entry.poss != 0).map (·.2)

-- the toy's own structure passes every clause
#guard clausesAt id == some [true, true, true, true, true, true, true]

-- 1. kinds, cuts, parameter bytes, statement, digest, random bytes: as Entry.read has them
#guard (declared.bind fun D => statementAt.bind fun x => linkSpec.bind fun S =>
  (D.spec D.link D.cfg x.bytes).map fun X =>
    [X.base.rounds.map (·.kind) == S.base.rounds.map (·.kind),
      X.base.rounds.map (·.items) == S.base.rounds.map (·.items),
      X.base.params == S.base.params, X.base.statement == S.base.statement,
      X.base.cfg == S.base.cfg,
      (match X.base.rand, S.base.rand with | .inFile, .inFile => true | _, _ => false)]) ==
  some [true, true, true, true, true, true]
-- with one root more in the entry of each round that sends a root, the cuts are others
#guard (declared.bind fun D => linkSpec.map fun S =>
  (D.link.rounds.map fun r =>
    let more := if r.entry.roots != 0 then 1 else 0
    ({ r with entry := { r.entry with roots := r.entry.roots + more } } : DeclaredRound).items) ==
      S.base.rounds.map (·.items)) == some false

-- 2. the cut of made-up entries
#guard ({ name := "x", msg := 24 * 2 + 32 * 3 + 24 * 4, roots := 3, answers := 2 } : Entry).cut ==
  [.answer, .answer, .root, .root, .root, .e, .e, .e, .e]
#guard ({ name := "x" } : Entry).cut == []
#guard ({ name := "x", msg := 56, roots := 1 } : Entry).cut == [.root, .e]
-- 25 bytes, and 24 bytes with a root of 32: no cut has them; 56 bytes with a root: an element more
#guard (declared.map fun D =>
  ([⟨{ name := "BAT", msg := 25 }, [], []⟩, ⟨{ name := "BAT", msg := 24, roots := 1 }, [], []⟩,
    ⟨{ name := "BAT", msg := 56, roots := 1 }, [], []⟩] : List DeclaredRound).map fun r =>
      D.chainOk { D.link with rounds := [r] }) == some [false, false, true]

-- 3. the digest of the declared files; any 32 bytes pass; the digest at the format's hash
#guard (declared.bind fun D => statementAt.map fun x =>
  (D.entryFormOkOwn x, D.entryFormOk zero32 x, Id.run (D.cfgW (m := Id) formatHash) == D.cfg,
    D.cfg == zero32)) == some (true, true, true, false)

-- 4. the shape's six words, each changed alone
-- the depth: the stored trees' and the item's
#guard clausesAt (fun D => { D with table := { D.table with a := 13 } }) ==
  some [true, true, true, true, false, false, false]
-- the entries of a row's message, and of its tail: the item's alone
#guard clausesAt (fun D => { D with table := { D.table with message := 804 } }) ==
  some [true, true, true, true, true, false, false]
#guard clausesAt (fun D => { D with table := { D.table with tail := 1000 } }) ==
  some [true, true, true, true, true, false, false]
-- the rows: the stored trees' width and the item's
#guard clausesAt (fun D => { D with table := { D.table with logRows := 4 } }) ==
  some [true, true, true, true, false, false, false]
-- the salt: the stored trees' and the item's
#guard clausesAt (fun D => { D with table := { D.table with saltBytes := 48 } }) ==
  some [true, true, true, true, false, false, false]
-- the stored trees' own depth, the shape kept: their shape against the tables', alone
#guard clausesAt (fun D => { D with link := { D.link with rounds := D.link.rounds.map fun r =>
    { r with stored := r.stored.map fun t => { t with sh := { t.sh with a := 13 } } } } }) ==
  some [true, true, true, true, false, true, false]
-- the setting's salt is another number than the tables': with 48 there every clause passes; with 39
-- the description is not in order, alone
#guard clausesAt (fun D => { D with setting := { D.setting with salt := 48 } }) ==
  some [true, true, true, true, true, true, true]
#guard clausesAt (fun D => { D with setting := { D.setting with salt := 39 } }) ==
  some [true, true, true, false, true, true, false]
-- the answers a row: the setting's number of answers to a sample, and the item's
#guard clausesAt (fun D => { D with table := { D.table with answers := 2 } }) ==
  some [false, true, true, true, true, false, false]

-- 5. a name that the format has not: no kind, so no description
#guard clausesAt (fun D => roundChanged D 0 fun r =>
    { r with entry := { r.entry with name := "FOLD eps" } }) ==
  some [true, false, true, false, true, true, false]
#guard (declared.bind fun D => statementAt.map fun x =>
  let D' := roundChanged D 0 fun r => { r with entry := { r.entry with name := "FOLD eps" } }
  (D'.spec D'.link D.cfg x.bytes).isNone) == some true
-- the four rounds that sample positions: LINK, CS, CS, BASE; each, made to open nothing, is refused
-- by the test on the chain
#guard (declared.map samplingRounds) == some [3, 11, 16, 18]
#guard (declared.bind fun D => statementAt.map fun x => (samplingRounds D).map fun i =>
  let D' := roundChanged D i fun r => { r with stored := [], opens := [] }
  (D'.chainOk D'.link, D'.entryFormOk D.cfg x)) == some (List.replicate 4 (false, false))
-- every tree of the chain's own named as taken over from chain 0: no chain is in front of the link
#guard clausesAt (fun D => { D with link := { D.link with rounds := D.link.rounds.map fun r =>
    { r with opens := r.opens.map fun o => (o.1, .taken 0 o.1.tree) } } }) ==
  some [true, true, false, false, true, true, false]
-- a round SEAL at the end: every clause with a name passes, and the whole says no
#guard clausesAt (fun D => { D with link := { D.link with
    rounds := D.link.rounds ++ [⟨{ name := "SEAL" }, [], []⟩] } }) ==
  some [true, true, true, true, true, true, false]

-- 6. the random bytes as item 1 of a made-up statement; the statement has no item 2
#guard (declared.map fun D =>
  let s := tableItem "table" zero32 [(1, 2, 3)] ++ item bindRootName (pattern 32)
  ((D.spec { D.link with rand := .item 1 } D.cfg s).map fun X =>
      match X.base.rand with
      | .given b => b == pattern 32
      | _ => false,
    (D.spec { D.link with rand := .item 2 } D.cfg s).isNone)) == some (some true, true)

/-- A table with one thing changed: a root of 31 bytes; an answer too few; the word w as the first
word of every answer, at the field's modulus and at one less. -/
def tablesChanged (t : TableSt) : List TableSt :=
  [{ t with root := t.root.extract 0 31 }, { t with answers := t.answers.dropLast },
   { t with answers := t.answers.map fun a => (18446744069414584321, a.2) },
   { t with answers := t.answers.map fun a => (18446744069414584320, a.2) }]

-- 7. the statement's form: at the toy's; with the first table changed; with the further one
#guard (declared.bind fun D => statementAt.map fun x =>
  (x.ok D, (tablesChanged x.first).map fun t => ({ x with first := t } : EntryStm).ok D,
    (tablesChanged x.further).map fun t => ({ x with further := t } : EntryStm).ok D)) ==
  some (true, [false, false, false, true], [false, false, false, true])

end OnBytes.Entry.RecordToy
