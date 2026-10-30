-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToyDeclared.lean: the premises of Declared.spec_ok_small, Declared.spec_ok_lt,
Declared.entryFormOk_count and Declared.entryFormOk_fitsWord (Fmt/ChainStmSmall.lean) are met together
at the toy of OnBytes/Entry/RecordToyFiles.lean.

The declared structure is read off the toy's parameter bytes: the link's rounds come from the
description that Entry.read makes. Its parameter bytes and statement are then compared with the
toy's files, byte for byte, so the tests speak of that toy. Under a setting whose salts have 39
bytes the description is not in order.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.TestRecordToy
import Fmt.ChainStmSmall
import Fmt.ParamsRead

namespace OnBytes.Entry.RecordToy
open Fmt

/-- The table that the entry file holds. -/
def furtherTable : Option Params.TableName :=
  firstTable.bind fun t =>
    match Entry.check entryParameters t entryFile with
    | .ok f => some f
    | .error _ => none

/-- The description of the link's chain, as Entry.read makes it. -/
def linkSpec : Option SpecX := do
  let p ← Params.Link.read entryParameters
  let t ← firstTable
  let f ← furtherTable
  match Entry.read p t entryFile with
  | .ok r => (r.block.rounds (Entry.start p)).bind (p.describe t f)
  | .error _ => none

/-- A tree of the chain's own, named: the link takes none over. -/
def sourceOf : Src → TreeSource
  | .own n => .own n
  | .given _ _ => .taken 0 0

/-- The link's chain, declared. -/
def linkDeclared : Option ChainDecl := linkSpec.map fun S =>
  { label := S.base.label
    record := true
    others := ((paramsRead entryParameters).map (·.others)).getD []
    rand := .inFile
    firstTree := S.base.firstTree
    rounds := (S.base.rounds.zip S.stored).map fun y =>
      ⟨y.1.entry, y.2, y.1.opens.map fun o => (o.1, sourceOf o.2)⟩ }

/-- The toy's declared structure. -/
def declared : Option Declared := linkDeclared.map fun l =>
  { files := [publicFileOne, publicFileTwo]
    setting := ⟨.two, 40, 8, 0, 1, 1⟩
    table := ⟨14, 803, 1001, 3, 1, 40⟩
    link := l }

/-- A coordinate triple of the present road as an element of Fmt. -/
def extOf (e : OnBytes.E) : Ext := (e.c0, e.c1, e.c2)

/-- The statement at the two tables. -/
def statementAt : Option EntryStm := do
  let t ← firstTable
  let f ← furtherTable
  pure ⟨⟨t.root, t.answers.map extOf⟩, ⟨f.root, f.answers.map extOf⟩⟩

-- the declared structure spells the toy's parameter bytes and statement
#guard (declared.map fun D => D.params D.link D.cfg == entryParameters) == some true
#guard (statementAt.map fun x => x.bytes == entryStatement) == some true
-- the two premises of Declared.spec_ok_small and Declared.spec_ok_lt are met together
#guard (declared.bind fun D => statementAt.bind fun x =>
  (D.spec D.link D.cfg x.bytes).map (·.ok)) == some true
-- under a setting whose salts have 39 bytes there is a description, and it is not in order
#guard (declared.bind fun D => statementAt.bind fun x =>
  (({ D with setting := { D.setting with salt := 39 } } : Declared).spec D.link D.cfg x.bytes).map
    (·.ok)) == some false
-- the two premises of Declared.entryFormOk_count and Declared.entryFormOk_fitsWord are met together
#guard (declared.bind fun D => statementAt.map fun x =>
  D.entryFormOk D.cfg x && x.ok D && D.table.count == 8) == some true

end OnBytes.Entry.RecordToy
