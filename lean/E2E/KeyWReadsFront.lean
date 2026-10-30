-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyWReadsFront.lean: at the written sizes W's sending reads challenges in front of it: the
batching's numbers lie below the rounds of the first seventeen sub-protocols.

  roundsTo_rows        roundsTo, by a list's rows
  battAt_full          the numbers: 18,828, 18,829, 18,830
  roundsTo_seventeen   18,848
  battAt_below         the column variables' last challenge is below it

Limits. keyPoints' stretch is keyPt_cut, not stated here. Nothing on any property.
-/
import E2E.KeyThePartsFacts
import E2E.KeyPlaces
import E2E.KeyPlacesNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Block Place)
open AtPublicFiles.KeyValues (blocksOf battAt oneOf)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open Johnson.RunOne.Sound (rowsOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest (roundsTo declsTo)

/-- The rounds of a list's first n rows. -/
def sumRows (n : Nat) (rows : List (Place × Nat)) : Nat := ((rows.take n).map (·.2)).sum

theorem roundsTo_rows {S Cl : Type} (bs : List (Block S Cl)) (n : Nat) :
    roundsTo bs n = sumRows n (rowsOf bs) := by
  unfold roundsTo declsTo sumRows
  induction bs generalizing n with
  | nil => simp [rowsOf]
  | cons b bs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have := ih n
      simp only [List.take_succ_cons, List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons, rowsOf, List.map_map] at this ⊢
      rw [this]

theorem batt_start_full : startIn fullFirst battPlace = some 18828 := by decide +kernel

theorem rows_seventeen_full : sumRows 17 fullFirst = 18848 := by decide +kernel

variable {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **The batching's numbers at the written sizes.** -/
theorem battAt_full (scope : InScope Z = true) (h : KeyNamed Z X N P) :
    battAt X N = ⟨18828, 18829, 18830⟩ := by
  obtain ⟨r1, -, -⟩ := places_named scope h
  have e : ProofFile.Honest.roundsInFront (blocksOf X N) battPlace = some 18828 := by
    rw [roundsInFront_rows]
    show startIn (rowsOf (keyFileDescription X N P).first.blocksInOrder) battPlace = _
    rw [r1]
    exact batt_start_full
  show (⟨(ProofFile.Honest.roundsInFront (blocksOf X N) battPlace).getD 0,
    (ProofFile.Honest.roundsInFront (blocksOf X N) battPlace).getD 0 + 1,
    (ProofFile.Honest.roundsInFront (blocksOf X N) battPlace).getD 0 + 2⟩ : AtPublicFiles.Key.BattAt) = _
  rw [e]
  rfl

/-- **The rounds of the first seventeen sub-protocols.** -/
theorem roundsTo_seventeen (scope : InScope Z = true) (h : KeyNamed Z X N P) :
    roundsTo (keyFileDescription X N P).first.blocksInOrder 17 = 18848 := by
  obtain ⟨r1, -, -⟩ := places_named scope h
  rw [roundsTo_rows, r1]
  exact rows_seventeen_full

/-- **What W's weights read lies in front of W.** -/
theorem battAt_below (scope : InScope Z = true) (h : KeyNamed Z X N P) {i : Nat} (hi : i < 18) :
    (battAt X N).sigma < roundsTo (keyFileDescription X N P).first.blocksInOrder 17 ∧
      (battAt X N).eps < roundsTo (keyFileDescription X N P).first.blocksInOrder 17 ∧
      (battAt X N).first + i < roundsTo (keyFileDescription X N P).first.blocksInOrder 17 := by
  rw [battAt_full scope h, roundsTo_seventeen scope h]
  show 18828 < 18848 ∧ 18829 < 18848 ∧ 18830 + i < 18848
  omega

end AtPublicFiles.KeyBook
