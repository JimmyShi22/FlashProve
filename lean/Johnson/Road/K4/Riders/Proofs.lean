-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/Proofs.lean: THE FOUR SENTENCES OF Riders/Statements.lean, PROVED: which
sorts of item ride at K4's row (under three tests on the table), and that three of the four sorts
ride back over K4's accept at their owners' own sentences. Statements (the sentences' own words) and
proofs.

  **`riders_are`** : `RidersAre`: by the bridge from the rule's open set to the table's list
    (`openIsList`, `openL_iff_openSets`: Johnson/Desc/Sound/SpineList.lean), then the test.
  **`rides_pile`** : `RidesPile`: in a feed-forward segment S.rows is out.pending, in front and
    behind.
  **`rides_row`** : `RidesRow`: the sentence reads st and book alone.
  **`rides_constr`** : `RidesConstr`: by the sentence's arms.

Limits. The three tests are premises of `riders_are`: none is evaluated here. The fourth sort,
formsT m 2 "objects", is not here. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.Riders.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Rest)
open VerifiableInference.Desc (Place Strs Wit)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item RowClass Numbers start openSets readsOpen
  rowSays wordsAtFirst classRows)
open VerifiableInference.Desc.First.FillK4 (isK4At)
open VerifiableInference.Desc.Sound (insQ outsQ openAfter insL outsL rowsApart MsgT openIsList
  openL_iff_openSets)

theorem riders_are : RidersAre := by
  intro links ps k m pl H hfit hr ha i ho hi
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp H.here).1
  have h1 : i ∈ (openSets links ps (start links))[k]?.getD [] :=
    (openL_iff_openSets links ps (start links) hr ha (by simp [start]) k (Nat.le_of_lt hk) i).1
      ((openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 ho)
  have h2 := List.all_eq_true.1 hfit k (List.mem_range.2 hk)
  rw [H.here] at h2
  have hK : isK4At links pl = true := by
    simp [isK4At, H.link, H.sub, H.piece]
  simp only [hK, Bool.not_true, Bool.false_or] at h2
  have h3 := List.all_eq_true.1 h2 i h1
  rw [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · exact absurd (by simpa using h3 : i ∈ insL links ps k) hi
  · rw [H.link] at h3
    exact h3

theorem rides_pile : RidesPile := by
  intro s s' a hR ha
  obtain ⟨a', ha', _⟩ := hR.here a ha
  unfold S.rows
  rw [ha, ha', hR.out]

theorem rides_row : RidesRow := by
  intro P Cells Tok N arr m c Z s s' y y' w hR
  have e1 : classRows N m c s' = classRows N m c s := by
    unfold classRows
    rw [hR.st, hR.book]
  unfold rowSays wordsAtFirst
  show _ ↔ _
  simp only [e1, hR.st, hR.book]

theorem rides_constr : RidesConstr := by
  intro X P W rows cols hd put H headPart digitsPart k p a b y y' w hDec hReq hHead hDig h
  unfold P5J.constrQAt at h ⊢
  by_cases hp : p = .lookDigits
  · rw [if_pos hp] at h ⊢
    exact hDig hp h
  · rw [if_neg hp] at h ⊢
    refine ⟨h.1, fun M i hM hH => ?_⟩
    have h2 := h.2 M i (hDec ▸ hM) hH
    by_cases hk : k = hd
    · rw [if_pos hk] at h2 ⊢
      exact hHead hk i h2
    · rw [if_neg hk] at h2 ⊢
      rw [hReq]
      exact h2

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.riders_are
#print axioms OnBytes.Road.K4.Riders.rides_pile
#print axioms OnBytes.Road.K4.Riders.rides_row
#print axioms OnBytes.Road.K4.Riders.rides_constr
