-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastNumbers.lean: the numbers and shapes that the last chain's premises name, in scope.

  `orc_two`: `ho₂` of `last_laid`: W is message 9.
  `S_third`, `S_par`, `codes_one`, `w_number`: `hS`', `hS`, `hc`, `hn` of `hv_door`.
  `hdot_own`: (Dot) at the key's door at the one (Dot), with these four paid.

Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastDoorDot

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (Source LaterPlaces thirdPar)
open AtPublicFiles.KeyValues (oneOf firstW)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.AtFiles (KeySourced CF SF)
open AtPublicFiles.AtFiles.Full (A0 six_sourced par_sourced QK)
open Lk6.AtPlan (keyFull keyX)
open Johnson.RunOne.KeyRows1 (plan₁)

theorem stages_X : keyX.stages.length = 4 := by decide +kernel

theorem S_QK : QK.par.S = SF := by decide +kernel

theorem w_written : 1 + (Wf.messageOf keyX).size +
    ((AtPublicFiles.TreeReads.sentOfTest keyFull.set.samples true keyX.stages).map List.length).sum = A0.2.w := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **W is message 9.** -/
theorem orc_two (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 2 = some 9 := by
  have hr : (AtPublicFiles.KeyThread.one₀ Xs).ranges = keyX := (six_sourced hs scope).ranges
  show some (1 + 2 * (AtPublicFiles.KeyThread.one₀ Xs).ranges.stages.length) = some 9
  rw [hr, stages_X]

theorem S_one (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) : (oneOf Xs).lin = SF :=
  (six_sourced hs scope).lin

theorem codes_one (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) : CF = (oneOf Xs).codes :=
  (six_sourced hs scope).codes.symm

theorem S_par (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (parKey Xs Pl).par.S = (oneOf Xs).lin := by
  have e : parKey Xs Pl = QK := par_sourced hs scope
  rw [e, S_QK, S_one hs scope]

theorem S_third (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (thirdPar Xs.chains).S = (oneOf Xs).lin := by
  obtain ⟨-, -, hlin, -⟩ := AtPublicFiles.AtFiles.Full.first_of_sourced hs scope fun _ _ _ _ => true
  exact (hlin.symm.trans (six_sourced hs scope).lin).trans (S_one hs scope).symm

theorem w_number (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) : A0.2.w = firstW Xs := by
  have hr : (oneOf Xs).ranges = keyX := (six_sourced hs scope).ranges
  have hm : (oneOf Xs).given.plan.samples = keyFull.set.samples := (six_sourced hs scope).samples
  show _ = 1 + (Wf.messageOf (oneOf Xs).ranges).size +
    ((AtPublicFiles.TreeReads.sentOfTest (oneOf Xs).given.plan.samples true (oneOf Xs).ranges.stages).map List.length).sum
  rw [hr, hm]
  exact w_written.symm

section
open OnBytes.Slice OnBytes.Means
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces thirdPar descriptionFromSource)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (VIs)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.KeyValues (oneOf firstW)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (KeySourced CF)
open AtPublicFiles.AtFiles.Full (A0)
open AtPublicFiles.FirstH (Th FirstPublic WPublic HeardOfFold LaterFill HCells HTab fillH tbH)
open AtPublicFiles.KeySharedThread (parKey randKey threadKey)
open AtPublicFiles.KeyThread (decl₁ laid₁)
open AtPublicFiles.KeyDoorItems (wit₃ commonOf)
open ProofFile.Honest
open ProofFile.Honest.K14 (WitLens holds2)
open VerifierAndGoals (PublicFiles InScope)

variable {W₀ Rc X₀ X' Wk P₂ Wt₂ : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Z : PublicFiles}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → ProofFile.Honest.Weights} {Q : LaterFill (keyBook K₀) W₀ Rc}
  {w₀ : W₀} {rc : Rc} {x : Xi}
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey)

/-- **(Dot) at the key's door, at the one (Dot)**: hdot_door with its four equations paid. -/
theorem hdot_own (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hw : WPublic Xs N Pl) (hF : HeardOfFold Xs N Pl)
    (hf : K.weights = f)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit))
    (D : MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words GE))
    (k : Coins (keyBook K₀)) {e₁ : FirstState} {m₁ : Mid (In1 W₀ Rc) X'} {E₁ : Env} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (Th Xs N Pl K f Q w₀ rc x) 19 k e₁ m₁ E₁)
    (u₂ : Thr (threadKey Xs N Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) 12 k e₂ m₂ E₂)
    (y : VerifiableInference.Desc.Strs) (ds : List Fmt.Drawn) :
    (AtPublicFiles.KeyDotItem.dotFill (thirdPar Xs.chains).S gKey
      (fun _ => wvK (val₁Key Xs (fillH Xs N Pl K f Q x)) (thirdPar Xs.chains).S CF A0.2.w) D).dot (x, e₁) e₂ y
      (wit₃ Xs N Pl K (fillH Xs N Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds))) := by
  have e : (parKey Xs Pl).par.S = (thirdPar Xs.chains).S := (S_par hs scope).trans (S_third hs scope).symm
  rw [← e]
  exact hdot_door ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ hs scope hK hp hw hF (S_par hs scope) (e ▸ S_par hs scope) (codes_one hs scope) (w_number hs scope) hf hw₂ D k u₁ u₂ y ds

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.stages_X
#print axioms AtPublicFiles.KeyLastChain.S_QK
#print axioms AtPublicFiles.KeyLastChain.w_written
#print axioms AtPublicFiles.KeyLastChain.orc_two
#print axioms AtPublicFiles.KeyLastChain.S_par
#print axioms AtPublicFiles.KeyLastChain.S_third
#print axioms AtPublicFiles.KeyLastChain.codes_one
#print axioms AtPublicFiles.KeyLastChain.w_number
#print axioms AtPublicFiles.KeyLastChain.hdot_own
