-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableSealRow.lean: WHAT THE SEAL's TIE ASKS OF THE TABLE (RowSeal,
Johnson/Desc/K13/Law/AtTableSeal.lean; and which items ride past the block) AS TESTS WITH CODE, WITH
MEMBERS AT BOTH LISTS. Definitions and statements with their proofs.

OBJECT. The table's own text (Johnson/Desc/First/Borders.lean), at the lists linksSmall | linksFull
(Johnson/Desc/K13/Law/AtTableRow.lean) and the door's filling wSitsMore.
USER. seal_tied | firstEnd_tied_seat | _lift's premise hT; firstEnd_tied_sig's hR.
FIELD. first_chain_knows_means (Johnson/Goal/Skeleton/ProofFile.lean), through chainOfPromises.

Main names:
  rowSealB · rowSeal_of_test · rowSeal_small · rowSeal_full   RowSeal as a test with code, and
    **members**: block number 77 of 78; 357 of 358. rowSeal_small_merged | _full_merged: the same
    at ({} : More).merge wSitsMore: the form of the table's files' own door at Mg₁.more := {}.
    rowSealB_other: tries.
  ridersB · riders_of_test · riders_small · riders_full   what is open in front of the seal is "no
    mark", the stored table's pin, the index masks' pin, W's pin or the one claim (on openAfter, by
    the list openL). openSealB · open_of_test · openSeal_both: the like on First.openSets.
What is not claimed. The members are of the table's half alone: the two equations on the plan's
numbers stay premises; the two lists are as the table's walk writes them: tied to no plan, to no
description's places, to no block; at a filling into which other kinds' items are merged (the
table's files' own door IS such a merge: at an Mg₁.more other than {}) the tests are to be run
anew. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.AtTableSeal
import Johnson.Desc.K13.Law.AtTableW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (ModelPart Item Pub Numbers More)
open VerifiableInference.Desc.Sound (insQ outsQ openAfter insL outsL openL openIsList)

/-- **RowSeal as a test with code.** -/
def rowSealB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | none => false
  | some p =>
    (First.rowOf links p).ins.isEmpty && (First.rowOf links p).outs.isEmpty &&
      (First.rowOf links p).ctx.isEmpty && !(First.rowOf links p).lays && ps[k + 1]?.isNone &&
      (First.standAt links p == .mem) && !First.mayWait links p &&
      (First.pubStep ((First.pubSets M links ps)[k]?.getD []) (First.pubRowM M links p)).all
        ((First.pubSets M links ps)[k]?.getD []).contains

/-- **A yes of the test gives what is asked of the table**, at every N that has as many trees and
messages behind the block as in front. -/
theorem rowSeal_of_test (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : rowSealB M links ps k = true) (N : Numbers)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?) :
    ∃ p, RowSeal N M links ps k p := by
  unfold rowSealB at h
  cases hp : ps[k]? with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h3'⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    exact ⟨p, hp, List.isEmpty_iff.1 h1, List.isEmpty_iff.1 h2, List.isEmpty_iff.1 h3,
      by simpa using h3', Option.isNone_iff_eq_none.1 h4, eq_of_beq h5, by simpa using h6,
      fun q hq => List.contains_iff_mem.1 (List.all_eq_true.1 h7 q hq), hT, hM⟩

set_option maxRecDepth 1000000 in
/-- **A member of the test** (the numbers' half is a premise): the small list; the seal has the
number 77 of 78. -/
theorem rowSeal_small (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.treesAt (First.flatPlaces true linksSmall true)[77]?)
    (hM : N.msgsAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.msgsAt (First.flatPlaces true linksSmall true)[77]?) :
    ∃ p, RowSeal N wSitsMore linksSmall (First.flatPlaces true linksSmall true) 77 p :=
  rowSeal_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- The full list: 357 of 358. -/
theorem rowSeal_full (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.treesAt (First.flatPlaces true linksFull true)[357]?)
    (hM : N.msgsAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.msgsAt (First.flatPlaces true linksFull true)[357]?) :
    ∃ p, RowSeal N wSitsMore linksFull (First.flatPlaces true linksFull true) 357 p :=
  rowSeal_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- **The same two at the door's filling merged into the empty one**: the form of the table's
files' own filling (mg1Joint's more := Mg₁.more.merge wSitsMore,
Johnson/Desc/Sound/JointFilling.lean) at Mg₁.more := {}. -/
theorem rowSeal_small_merged (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.treesAt (First.flatPlaces true linksSmall true)[77]?)
    (hM : N.msgsAt (First.flatPlaces true linksSmall true)[77 + 1]? =
      N.msgsAt (First.flatPlaces true linksSmall true)[77]?) :
    ∃ p, RowSeal N (({} : More).merge wSitsMore) linksSmall
      (First.flatPlaces true linksSmall true) 77 p :=
  rowSeal_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
theorem rowSeal_full_merged (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.treesAt (First.flatPlaces true linksFull true)[357]?)
    (hM : N.msgsAt (First.flatPlaces true linksFull true)[357 + 1]? =
      N.msgsAt (First.flatPlaces true linksFull true)[357]?) :
    ∃ p, RowSeal N (({} : More).merge wSitsMore) linksFull
      (First.flatPlaces true linksFull true) 357 p :=
  rowSeal_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- Tries: one block earlier (W's sending), and one border later, the test says no. -/
theorem rowSealB_other :
    rowSealB wSitsMore linksSmall (First.flatPlaces true linksSmall true) 76 = false ∧
      rowSealB wSitsMore linksSmall (First.flatPlaces true linksSmall true) 78 = false := by
  decide +kernel

/-- **The fact on the table, as a test with code**: what is open in front of block k is "no mark",
the stored table's pin, the index masks' pin, W's pin or the one claim. -/
def ridersB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  (openL (insL links ps) (outsL links ps) (First.start links) k).all fun i =>
    i == .unmarked || i == .pinW || i == .pinI || i == .pinV || i == .pileOne

/-- A yes of the test gives the riders, where "no mark" is among what the row closes or reads. -/
theorem riders_of_test (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : ridersB links ps k = true) (i : Item)
    (hi : openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i ∧
      ¬ insQ links ps k i) : i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne := by
  have hm := (openIsList Item (insL links ps) (outsL links ps) (First.start links) k i).1 hi.1
  have hb := List.all_eq_true.1 h i hm
  simp only [Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with (((rfl | e) | e) | e) | e
  · exact absurd (List.mem_append_right _ (List.mem_singleton.2 rfl)) hi.2
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr e))

set_option maxRecDepth 1000000 in
/-- **Members**: at both lists, in front of the seal. -/
theorem riders_small : ridersB linksSmall (First.flatPlaces true linksSmall true) 77 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem riders_full : ridersB linksFull (First.flatPlaces true linksFull true) 357 = true := by
  decide +kernel

/-- **The like on the table's own open set** (First.openSets): a test with code. -/
def openSealB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  (openAt links ps k).all fun i =>
    i == .unmarked || i == .pinW || i == .pinI || i == .pinV || i == .pileOne

theorem open_of_test (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : openSealB links ps k = true) :
    ∀ i ∈ openAt links ps k, i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne := by
  intro i hi
  have hb := List.all_eq_true.1 h i hi
  simp only [Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with (((e | e) | e) | e) | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr e)))

set_option maxRecDepth 1000000 in
theorem openSeal_both :
    openSealB linksSmall (First.flatPlaces true linksSmall true) 77 = true ∧
      openSealB linksFull (First.flatPlaces true linksFull true) 357 = true := by
  decide +kernel

end VerifiableInference.Desc.K13.Law
