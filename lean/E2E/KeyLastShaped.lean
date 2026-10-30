-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastShaped.lean: the last thread's first shape: `ThirdShaped` at `T₃K`, at every list of challenges. Where a pair of
earlier stands lies behind the list, `first₃_shape` pays it; elsewhere `endsKey` returns its default, and at a default
whose first state names no claim the start refuses, so the thread begins nowhere there.

  `third_shaped`: the premise of 'accepted_third₀', `₁`, `₃` and of `shape_own`.

What stays open. hd: the default names no claim: a choice of the letter d. hfit: the key fits, at whatever the shared
thread's input is. That any pair stands.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastDoor
import E2E.KeyQuietThird
import E2E.KeyShapeThirdFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St first)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey sits_two parKey)
open AtPublicFiles.KeyThread (KeyFill laid₁)
open AtPublicFiles.KeyDoorItems (commonOf)
open AtPublicFiles.KeyDoorPairs (endsKey endsPair)
open AtPublicFiles.KeyLastThread (handOf)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped)
open AtPublicFiles.AtFiles.Full (A0 shape19_of_thr shape12_of_thr QK yes₃_sourced first₃_shape)

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
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- **The last thread begins only at the written shape.** -/
theorem third_shaped (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    ThirdShaped (X := Xs) (N := Nr) (P := Pl) (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
      Kp w) v A0 := by
  refine ⟨yes₃_sourced hs scope v, fun k u h s₀ _ hb => ?_⟩
  have hb' : (descriptionFromSource Xs Nr Pl).start₃
      (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k u h).1.1
      (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k u h).1.2
      (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k u h).2 = .ok s₀ := hb
  by_cases hE : ∃ p : FirstState × St, ∃ (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env)
      (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k p.1 m₁ E₁ ∧
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k p.2 m₂ E₂ ∧
      m₁.st.input = u ∧ m₂.st.input = commonOf u ∧ m₁.st.heard ++ m₂.st.heard = h
  · have e : endsPair Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k u h = hE.choose := by
      unfold endsPair endsBy
      exact dif_pos hE
    obtain ⟨a₁, F₁, a₂, F₂, v₁, v₂, -, -, -⟩ := hE.choose_spec
    have h1 := shape19_of_thr hs scope (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) rfl
      (fun _ _ _ _ _ hb => ⟨_, hb⟩) v₁.1
    have h2 := shape12_of_thr hs scope (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
      (sits_two Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).2.2.2.1
      (fun _ c _ t hv hb => ⟨⟨c.key⟩, by
        have q : t = first (parKey Xs Pl).codes c.key := hb
        rw [q]
        rfl, hfit c hv⟩) v₂.1
    unfold endsKey at hb'
    rw [e] at hb'
    exact first₃_shape hs scope v u.x _ _ h1 h2 s₀ hb'
  · have e : endsPair Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k u h =
        (d.1.2, d.2) := by
      unfold endsPair endsBy
      exact dif_neg hE
    unfold endsKey at hb'
    rw [e] at hb'
    obtain ⟨f, o, hh, -⟩ := (AtPublicFiles.KeyLastThread.start_key Xs Nr Pl u.x d.1.2 d.2 s₀).1 hb'
    have hh' : d.1.2.lin.map (handOf d.1.2) = some f := hh
    rw [hd] at hh'
    cases hh'

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.third_shaped
