-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastEnd.lean: at a stand of the last thread at border 0 the handed shared state has Omega at number 2 and the written codes: from the written shape alone. The premise `hend` of `dot_stand`.

  `end_of_shape`: at the start's state.
  `end_stand`: at a stand.

Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnSayAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey Part)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (ended_shared)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.KeyLastThread (start_key)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped Sh₃ sh₃ SF CF borderSh)
open AtPublicFiles.AtFiles.Full (A0)

/-- **At the start's state.** -/
theorem end_of_shape {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {x : Xi} {f : FirstState} {e : St} {s₀ : S₃}
    (hst : (descriptionFromSource Xs Nr Pl).start₃ x f e = .ok s₀) (hsh : sh₃ SF s₀ = A0) : e.loc.oOmega = 2 ∧ e.st.codes = CF := by
  obtain ⟨h, o, -, ho, hs'⟩ := (start_key Xs Nr Pl x f e s₀).1 hst
  have ho' : (_root_.Desc.K14.ended e).map VerifiableInference.Desc.Third.sharedOfEnd = some o := ho
  obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.1 ho'
  obtain ⟨-, eo, est, -⟩ := ended_shared _ e' he'
  obtain ⟨⟨g, hb⟩, -⟩ := K14.start_gives (thirdPar Xs.chains) _ _ s₀ hs'
  have q₁ : (sh₃ SF s₀).2.border.map (·.omega) = some 2 := by
    rw [hsh]
    exact omega_border_A0
  have q₂ : (sh₃ SF s₀).2.border.map (·.st.codes) = some CF := by
    rw [hsh]
    exact codes_border_A0
  have r₁ : (s₀.loc.border.map (borderSh SF s₀.st.codes)).map (·.omega) = some 2 := q₁
  have r₂ : (s₀.loc.border.map (borderSh SF s₀.st.codes)).map (·.st.codes) = some CF := q₂
  rw [hb] at r₁ r₂
  exact ⟨eo.symm.trans (Option.some.inj r₁), est.symm ▸ Option.some.inj r₂⟩

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
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

/-- **At a stand at border 0.** -/
theorem end_stand (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hZ : ThirdShaped (X := Xs) (N := Nr) (P := Pl) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) (fun _ _ _ => true) A0)
    {k : Coins Bk} {s : S₃} {m : Mid (Local W₀ Rc Xi Unit) X} {E : Env}
    (hT : Thr (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) 0 k s m E) :
    ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM).seat k m s).1.2.loc.oOmega = 2 ∧ ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM).seat k m s).1.2.st.codes = CF := by
  have hsh := shape_zero hs scope rfl hZ hT
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hT.2.2.2.2.1
  have hs₀ : s₀ = s := by
    have q : (Except.ok (s₀, _, cols) : Except String (S₃ × List Fmt.RoundView × List OpenedColumn)) = .ok (s, [], []) := hf
    exact (Prod.mk.inj (Except.ok.inj q)).1
  subst hs₀
  exact end_of_shape hbeg hsh

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.end_of_shape
#print axioms AtPublicFiles.KeyLastChain.end_stand
