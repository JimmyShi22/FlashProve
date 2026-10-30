-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/MasksDoor.lean: THREE FILLINGS OF THE DOOR of the table of joints
(`First.More`, Johnson/Desc/First/Borders.lean): the public items "K13.pileMasks" (every row on the
table names mask entries of the index masks' message alone), "K13.pileWithin" (every ledger is that
of so many takes since it was made, and every such entry lies within its table) and "K13.oneRow"
(where the chain stands at its end: one row on the table, with a mask entry). Definitions; no
theorem. It imports the table alone.
Why. The items "every pending row holds" and "the one claim holds" read a row's mask entries through
the record's own book. That they read no other message than the one that the table books for them
holds only where the rows name that message alone. The sentence is an invariant of the rows on the
table: true of the empty pile by the first record's make; earned anew by whoever lays a pending row,
and by kind K13's block, which lays the one row.
The rows. Open at the chain's start; asked by kind K13's block and by W's commitment; dropped by
nobody on this chain (the one claim rides to the chain's end). "K13.pileWithin": the same rows.
"K13.oneRow": open at the chain's start, where it says nothing; asked by W's commitment; dropped by
nobody: NO ROW MAKES IT: kind K13's block earns it as an item that rides.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (Pub More)

/-- **Through the table's door**: "the rows on the table name the index masks' message alone". -/
def pileMasksItem : Pub := .more none "K13.pileMasks"

/-- The door's filling. -/
def pileMasksMore : More where
  rows := fun _ p =>
    if p.link.isNone && (p.kind == .K13 || p.kind == .K1) then
      { asks := [(none, "K13.pileMasks")] }
    else {}
  start := [(none, "K13.pileMasks")]

/-- "Every ledger fits, and the rows' mask entries lie within their tables". -/
def pileWithinItem : Pub := .more none "K13.pileWithin"

/-- The door's filling. -/
def pileWithinMore : More where
  rows := fun _ p =>
    if p.link.isNone && (p.kind == .K13 || p.kind == .K1) then
      { asks := [(none, "K13.pileWithin")] }
    else {}
  start := [(none, "K13.pileWithin")]

/-- "Where the chain stands at its end: one row on the table, with a mask entry". -/
def oneRowItem : Pub := .more none "K13.oneRow"

/-- The door's filling. -/
def oneRowMore : More where
  rows := fun _ p =>
    if p.link.isNone && p.kind == .K1 then { asks := [(none, "K13.oneRow")] } else {}
  start := [(none, "K13.oneRow")]

end VerifiableInference.Desc.K13.Law
