-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormRowsSeat.lean: THE FORM's HALF: the letters for saying that the link's three
kinds of rows pass ALL tests of a new open row at a record.

What is proved of them: Johnson/Prover/Link/FormRowsLaws.lean.

Main names.
  PadsFar T S u    the public places of the fold's own pad on its main table lie beyond the entries
    that the folded row takes (Beyond, FormPads.lean; FoldeqShape.entries, OnBytes/Iop/Foldeq.lean).
  FoldSeat T G S u A RECORD OF PREMISES: the fold u at the statement T and the group G: the
    soundness side's own
    PlacedU (Johnson/Desc/K14/Law/LawRL.lean: it has a main table of its layout's size, which holds
    a row's message and its random tail); it is a member of G; no test of G has begun; the table has
    at most 63 index bits; the table's shape is in order; PadsFar.

Limits. Letters: nothing says here that a record meets them.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormPadsRows
import Johnson.Desc.K14.Law.LawRL
import Johnson.Desc.First.Batch.Law.DoorTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params

/-- The places of the fold's own pad on its main table lie beyond the folded row's entries. -/
def PadsFar (T : Statement) (S : FoldeqShape) (u : FoldedRow) : Prop :=
  ∀ x, T.oracles[u.oracle]? = some x → ∀ q ∈ x.pad, q.1 = .main → Beyond u.lay S.entries q.2

/-- **A fold at a statement and a group.** -/
structure FoldSeat (T : Statement) (G : Group) (S : FoldeqShape) (u : FoldedRow) : Prop where
  placed : Desc.K14.Law.PlacedU T S u
  member : u.oracle ∈ G.members
  idle : G.inRun = false
  bits : u.lay.bits ≤ 63
  shape : S.index.ok = true
  far : PadsFar T S u

end Johnson.Prover.Link
