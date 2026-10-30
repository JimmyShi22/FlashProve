-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSeats.lean: THE FORM's HALF AT THE LINK's FRONT: the letter for what is
carried from behind the two joinings to the proximity test's front.

What is proved of it: Johnson/Prover/Link/FormSeatsLaws.lean.

Main names.
  LinkSeats p d G   A RECORD OF PREMISES on the link's carried record d: the group that the small
    record names is there, and is G; both folds are seated at it (FoldSeat,
    Johnson/Prover/Link/FormRowsSeat.lean); gamma has a coordinate for each bit of a table's row
    number; EVERY CLAIM THAT LIES OPEN ON G meets the soundness side's sentences for the tests of a
    new open row,
    at this statement and this group (RowClauses, Johnson/Desc/First/Batch/Law/DoorTests.lean).

Limits. A letter: nothing says here that a record meets it.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormMake
import Johnson.Desc.Link.LinkDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc
open Desc.K15 (St Par15)

/-- **What is carried behind the two joinings.** -/
structure LinkSeats (p : Par15) (d : St) (G : Group) : Prop where
  group : d.st.groups[d.loc.g]? = some G
  s0 : FoldSeat d.st G (p.S.side false p.samples) d.loc.o0
  s1 : FoldSeat d.st G (p.S.side true p.samples) d.loc.o1
  gamma : d.loc.gamma.length = p.S.table.v
  rows : ∀ row ∈ G.rows.toList, K9L.RowClauses d.st G row

end Johnson.Prover.Link
