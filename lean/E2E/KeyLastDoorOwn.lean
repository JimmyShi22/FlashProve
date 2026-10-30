-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastDoorOwn.lean: the door at the last thread of this work and its letter: `door_behind_key` with the clause that at the
door the run is the play of nothing from `startKey`.

  `door_mid`: the door's state is `doorMid`.
  `door_own`: `DoorBehindS` at `threadOwn`, `saidOwn`.

What stays open. The premises of `door_behind_key` but `hr`. `OneStand` at both last borders, beside `OneState`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill laid₁ lengths)
open AtPublicFiles.KeyDoorItems (commonOf wit₃)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK)

/-- The door's state is of the form `doorMid`. -/
theorem door_mid {W₀ Rc Xi' Ky Tr X₀ X : Type} (H : Prover W₀ Rc Xi' Ky Tr X₀ X) (R : Ready W₀ Rc Xi' Ky Tr X₀ X)
    (m₁ : Mid (Local W₀ Rc Xi' Tr) X) (m₂ : Mid (Common W₀ Rc Ky) X₀) (c : List OpenedColumn) :
    ({ R.start₃ H m₁ m₂ with opened := some c } : Mid (Local W₀ Rc Xi' Tr) X) = doorMid H R.own m₁ m₂ c := rfl

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

/-- **From the door at `saidLast`, the door at `saidOwn`.** -/
theorem door_own (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (a₁ : OneStand Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length)
    (a₂ : OneStand Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩)
    (hD : DoorBehindS (descriptionFromSource Xs Nr Pl) (keyProver K) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) Said₁ Said₂
      (saidLast (descriptionFromSource Xs Nr Pl) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)) x k R) :
    DoorBehindS (descriptionFromSource Xs Nr Pl) (keyProver K) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) Said₁ Said₂ (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) x k R := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ c₁ c₂ u₁ u₂ hh j₁ j₂
  obtain ⟨t, r⟩ := hD e₁ m₁ E₁ e₂ m₂ E₂ s₃ c₁ c₂ u₁ u₂ hh j₁ j₂
  refine ⟨t, r, fun _ => ?_⟩
  have hl := lengths scope hs.named
  have i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩ := by
    have v := u₁
    rw [hl.1] at v
    exact v.1.2.2.2.2.2.2.1
  have i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit) := by
    have v := u₂
    rw [hl.2.1] at v
    exact (v.1.2.2.2.2.2.2.1).trans hw₂
  have fr := last_front (T₃ := threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) rfl rfl
    (ahead_last Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML _ n₁ n₂ Vd _ _ w) u₁.1 u₂.1
  refine played_door (F := descriptionFromSource Xs Nr Pl) (T₃ := threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) fr ?_
  have hd : DoorState (keyProver K) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₁ Said₂
      (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length commonOf k R.own
      (m₁.st.heard ++ m₂.st.heard) (doorMid (keyProver K) R.own m₁ m₂ (c₁ ++ c₂)) :=
    ⟨e₁, m₁, E₁, e₂, m₂, E₂, c₁, c₂, u₁, u₂, by rw [hown]; exact i₁, by rw [hown]; exact i₂, rfl, j₁, j₂, rfl⟩
  rw [hl.1, hl.2.1] at hd
  rw [hl.1] at a₁
  rw [hl.2.1] at a₂
  exact startBy_eq dfltM a₁ a₂ hd

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.door_mid
#print axioms AtPublicFiles.KeyLastChain.door_own
