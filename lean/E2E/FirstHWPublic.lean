-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHWPublic.lean: `WPublic` (E2E/FirstHEval.lean), in scope.

  `roundsTo_rows`: the rounds in front of a border, off the list of places and their numbers of rounds.
  `w_public`: the closed facts on W's shape.

Limits. At the written sizes. Nothing on any property.
-/
import E2E.FirstHEval
import E2E.KeyPlacesNamed
import E2E.KeyEvalSays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Source LaterPlaces pieces)
open AtPublicFiles.KeyThread (D)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (six_sourced)
open AtPublicFiles.KeyValues (oneOf blocksOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- **The rounds in front of a border.** -/
theorem roundsTo_rows {S Cl : Type} : ∀ (bs : List (Block S Cl)) (b : Nat),
    roundsTo bs b = (((Johnson.RunOne.Sound.rowsOf bs).take b).map (·.2)).sum
  | [], b => by simp [roundsTo, declsTo, Johnson.RunOne.Sound.rowsOf]
  | _ :: _, 0 => rfl
  | x :: bs, b + 1 => by
    have e := roundsTo_rows bs b
    unfold roundsTo declsTo at e ⊢
    simp only [List.take_succ_cons, List.flatMap_cons, List.length_append, e]
    simp [Johnson.RunOne.Sound.rowsOf]

/-- At the written list of the first chain. -/
theorem base_written : (AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullFirst AtPublicFiles.KeyBook.battPlace).getD 0 =
    ((AtPublicFiles.KeyBook.fullFirst.take 16).map (·.2)).sum := by decide +kernel

variable {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Z : PublicFiles}

/-- **The closed facts on W's shape**, in scope. -/
theorem w_public (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) : WPublic Xs N Pl := by
  have six := six_sourced hs scope
  have hcodes : (oneOf Xs).codes = Lk6.AtPlan.keyFull.codes := six.codes
  have hlin : (oneOf Xs).lin = Lk6.AtPlan.keyFull.once.shape := six.lin
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := AtPublicFiles.Key.w_written
  obtain ⟨hbits, hfit⟩ := AtPublicFiles.Key.fit_one_row (oneOf Xs) (by rw [hlin]; exact a4) (by rw [hlin]; exact a5)
    (by rw [hlin, hcodes]; exact a6) (by rw [hlin, hcodes]; exact a7)
  refine ⟨by rw [hlin]; exact a1, by rw [hlin]; exact a2, by rw [hlin]; exact a3, hbits, hfit, ?_⟩
  have r1 : Johnson.RunOne.Sound.rowsOf (D Xs N Pl).first.blocksInOrder = AtPublicFiles.KeyBook.fullFirst :=
    (AtPublicFiles.KeyBook.places_named scope hs.named).1
  have a := AtPublicFiles.KeyBook.roundsInFront_rows (D Xs N Pl).first.blocksInOrder AtPublicFiles.KeyBook.battPlace
  have b := roundsTo_rows (D Xs N Pl).first.blocksInOrder 16
  rw [r1] at a b
  show (roundsInFront (D Xs N Pl).first.blocksInOrder AtPublicFiles.KeyBook.battPlace).getD 0 =
    roundsTo (D Xs N Pl).first.blocksInOrder 16
  rw [a, b]
  exact base_written

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.roundsTo_rows
#print axioms AtPublicFiles.FirstH.base_written
#print axioms AtPublicFiles.FirstH.w_public
