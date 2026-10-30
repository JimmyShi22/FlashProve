-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsSharedTestsFields.lean: the two fields `testOnFoldedRow` and `testOnOmega` of `KeyOthersPlay`
(E2E/OfflineRunsKey.lean), in the fields' own type (`PlaysAtShared`), at the written book.

  `testOnFoldedRow_at_parts`, `testOnOmega_at_parts`   at every parts K whose shape splits and whose two last halves of
        the shared chain are `proverSideOfTestOnU` and `proverSideOfTestOnOmega` at the written parameters and the written places' numbers, at every
        eight, stored columns and readers
  `testOnFoldedRow_at_value`, `testOnOmega_at_value`   at the offline prover's own senders (`valueAt`,
        E2E/KeyValueHolds.lean), at its two places' own numbers

Limits: those of E2E/OfflineRunsSharedTests.lean. The book is not free: that the two parts' readers agree is read off the
written book's ties. Nothing on any property.
-/
import E2E.OfflineRunsSharedTests
import E2E.OfflineRunsKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14 (SendPub)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyLay (proverSideOfTestOnU proverSideOfTestOnOmega)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt place_p12At)
open VerifierAndGoals (PublicFiles InScope)

section Parts
variable {W₀ Rc X₀ X Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **The field `testOnFoldedRow`**, at parts whose half at the place is `proverSideOfTestOnU` at the written values. -/
theorem testOnFoldedRow_at_parts (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK₀ : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ X Wk) (hsp : K.lin.S.sharedSplitNeeded = true)
    (hO : K.onOmega.place = omegaTestPlace) (A : SendPub) (hA : A = ⟨QK, 0⟩)
    (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (hU : K.onU = proverSideOfTestOnU A (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights rand)
    (common : Common W₀ Rc TableKey) :
    PlaysAtShared (keyFileDescription Xs N Pl) (keyBook K₀) (keyProver K) common foldedTestPlace := by
  have hPl : Pl = PF := later_sourced hs scope
  subst hPl
  intro j b hj hp
  obtain rfl := sharedBlock_folded hs scope b (List.mem_of_getElem? hj) hp
  have fU := (shared_finds K hsp (by rw [hU]; exact place_p12At _ _) hO).1
  rw [hU] at fU
  exact foldedTest_blockPlays K₀ hK₀ A hA _ bs st weights rand fU _

/-- **The field `testOnOmega`**, at parts whose half at the place is `proverSideOfTestOnOmega` at the written values. -/
theorem testOnOmega_at_parts (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK₀ : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ X Wk) (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU.place = foldedTestPlace) (A : SendPub) (hA : A = ⟨QK, 0⟩) (pU : P12)
    (bs : List (Block St Unit)) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand)
    (hO : K.onOmega = proverSideOfTestOnOmega A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand)
    (common : Common W₀ Rc TableKey) :
    PlaysAtShared (keyFileDescription Xs N Pl) (keyBook K₀) (keyProver K) common omegaTestPlace := by
  have hPl : Pl = PF := later_sourced hs scope
  subst hPl
  intro j b hj hp
  obtain rfl := sharedBlock_omega hs scope b (List.mem_of_getElem? hj) hp
  have fO := (shared_finds K hsp hU (by rw [hO]; exact place_p12At _ _)).2
  rw [hO] at fO
  exact omegaTest_blockPlays K₀ hK₀ A hA _ pU bs weights rand fO _ fun _ h => h.opened

end Parts

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **The field `testOnFoldedRow` at the offline prover's own senders.** -/
theorem testOnFoldedRow_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK₀ : fullPub = some K₀) (common : Common W₀ Rc TableKey) :
    PlaysAtShared (keyFileDescription Xs N Pl) (keyBook K₀)
      (keyProver (valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
        (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first)) common foldedTestPlace :=
  fun j b hj hp => sharedTests_shared_at_value K' Xs N Pl f g inR d ent groups first hs scope hK₀ common
    j b hj (Or.inl hp)

/-- **The field `testOnOmega` at the offline prover's own senders.** -/
theorem testOnOmega_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK₀ : fullPub = some K₀) (common : Common W₀ Rc TableKey) :
    PlaysAtShared (keyFileDescription Xs N Pl) (keyBook K₀)
      (keyProver (valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
        (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first)) common omegaTestPlace :=
  fun j b hj hp => sharedTests_shared_at_value K' Xs N Pl f g inR d ent groups first hs scope hK₀ common
    j b hj (Or.inr hp)

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.testOnFoldedRow_at_parts
#print axioms AtPublicFiles.OfflineRows.testOnOmega_at_parts
#print axioms AtPublicFiles.OfflineRows.testOnFoldedRow_at_value
#print axioms AtPublicFiles.OfflineRows.testOnOmega_at_value
