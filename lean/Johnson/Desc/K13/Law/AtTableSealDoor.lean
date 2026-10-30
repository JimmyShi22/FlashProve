-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableSealDoor.lean: WHAT THE SEAL's TIE ASKS OF THE TABLE (RowSeal,
Johnson/Desc/K13/Law/AtTableSeal.lean) AT EVERY DOOR WHOSE ROW AT THE SEAL MAKES NOTHING. Statements
with their proofs; no definition.

Why. Of RowSeal's clauses one alone reads the door's filling: "no public item comes at the block".
The members (Johnson/Desc/K13/Law/AtTableSealRow.lean) stand at wSitsMore, bare and merged into the
empty door. At a meaning that bears another kind's layer (the weights'
item) the door is not empty: there the members fit nothing. Here: the clause holds at every door
that makes nothing at the seal's place; the other clauses do not read the door.

OBJECT   First.pubStep · First.pubRowM: the table's own text.
USER     hT of seal_tied | firstEnd_tied_* | seal_seatLaws, at a composed meaning's door.
FIELD    first_chain_knows_means (Johnson/Goal/Skeleton/ProofFile.lean), through chainOfPromises.

  pubs_of_no_makes     a row that makes nothing lets no public item come.
  rowSeal_door         RowSeal from one door to another that makes nothing at the place.
  seal_place_small | _full   the place at 77 | 357 is placeSeal.
  rowSeal_small_door | rowSeal_full_door   **members at every such door**, at the two written lists.
What is not claimed. As AtTableSealRow.lean. That a composed door makes nothing at the seal: a test
on that door: one line. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.AtTableSealRow
import Johnson.Desc.K13.Law.OpenAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (ModelPart Pub Numbers More PubRow pubStep pubRowM pubRowOf pubSets
  moreItem)

/-- A row that makes nothing lets no public item come. -/
theorem pubs_of_no_makes (Q : List Pub) (r : PubRow) (h : r.makes = []) :
    ∀ q ∈ pubStep Q r, q ∈ Q := by
  intro q hq
  unfold pubStep at hq
  rw [h] at hq
  rcases List.mem_append.1 hq with hq | hq
  · exact (List.mem_filter.1 hq).1
  · cases hq

/-- **RowSeal from one door to another that makes nothing at the place.** -/
theorem rowSeal_door {N : Numbers} {M₀ : More} {links : List ModelPart} {ps : List Place} {k : ℕ}
    {p : Place} (h : RowSeal N M₀ links ps k p) (M : More) (h0 : (pubRowOf links p).makes = [])
    (hM : (M.rows links p).makes = []) : RowSeal N M links ps k p :=
  { h with
    pubs := pubs_of_no_makes _ _ (by
      show (pubRowOf links p).makes ++ (M.rows links p).makes.map moreItem = []
      rw [h0, hM]
      rfl) }

set_option maxRecDepth 1000000 in
/-- The place at 77 of the small list is the seal's. -/
theorem seal_place_small : (First.flatPlaces true linksSmall true)[77]? = some placeSeal := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem seal_place_full : (First.flatPlaces true linksFull true)[357]? = some placeSeal := by
  decide +kernel

/-- **A member at every door that makes nothing at the seal**: the small list. -/
theorem rowSeal_small_door (N : Numbers) (M : More)
    (hM : (M.rows linksSmall placeSeal).makes = [])
    (hT : N.treesAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.treesAt (First.flatPlaces true linksSmall true)[77]?)
    (hMs : N.msgsAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.msgsAt (First.flatPlaces true linksSmall true)[77]?) :
    RowSeal N M linksSmall (First.flatPlaces true linksSmall true) 77 placeSeal := by
  obtain ⟨p, h⟩ := rowSeal_small N hT hMs
  obtain rfl : p = placeSeal := Option.some.inj (h.place.symm.trans seal_place_small)
  exact rowSeal_door h M rfl hM

/-- The full list. -/
theorem rowSeal_full_door (N : Numbers) (M : More)
    (hM : (M.rows linksFull placeSeal).makes = [])
    (hT : N.treesAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.treesAt (First.flatPlaces true linksFull true)[357]?)
    (hMs : N.msgsAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.msgsAt (First.flatPlaces true linksFull true)[357]?) :
    RowSeal N M linksFull (First.flatPlaces true linksFull true) 357 placeSeal := by
  obtain ⟨p, h⟩ := rowSeal_full N hT hMs
  obtain rfl : p = placeSeal := Option.some.inj (h.place.symm.trans seal_place_full)
  exact rowSeal_door h M rfl hM

end VerifiableInference.Desc.K13.Law
