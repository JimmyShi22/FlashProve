-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontVProofs.lean: the proofs of the statements of Cb/Ld/LdFrontV.lean.

Main names (statements and hypotheses: Cb/Ld/LdFrontV.lean):
  `frontV_lo`, `frontV_sh`, `idleV_fresh`: see their statements in Cb/Ld/LdFrontV.lean.
  `frontV_forgetLo`, `frontV_forgetSh`: at the front p = nil ; split ; step, the annotated links of
    `ldFrLo`, `ldFrSh` are `p.cA false`, `p.cA true`.
Lo: the splitting in every slot; Sh: the splitting by the shared part.

Limits: what the head of Cb/Ld/LdFrontV.lean lists as not said is not said here either.
-/
import Cb.Ld.LdFrontV
import Cb.Ld.LdFrontBProofs
import Cb.Ld.LdLinCloseAltProofs
import Ior.LinkVMaskedRulesProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the link that does nothing does not look, for any readings -/
theorem idle_blindV {E : Type} [Field E] (a : LdStage E Unit) (N : ℕ) (VA : JV N a.J) (K0 Kj : Type)
    (k0 : VA.W0 → K0) (kj : a.J.W → Kj) (M0 Mj : Type) (put0 : M0 → K0 → K0) (putj : Mj → Kj → Kj) :
    (a.idLink.loV N VA VA.tie VA.q).hv.BlindV k0 kj k0 kj M0 Mj put0 putj put0 putj :=
  blindV_local _ _ _ _ a.idLink.R _ _ VA.W0 a.idLink.H K0 Kj Kj k0 kj kj M0 Mj put0 putj putj
    (blind_stepPure _ _ _ _ _ _ (fun x => some x) (ExtMap.id a.Ex) (fun p => p)
      _ _ kj kj Mj putj putj fun _ _ _ _ hk => ⟨rfl, hk⟩)

theorem idleV_fresh :
    Spec.idleV_fresh := fun _ _ a N VA _ _ c₀ K0 Kj k0 kj M0 _ _ put0 Mj _ _ putj h =>
  (ChainV.freshForV_snoc c₀ _ k0 kj M0 put0 Mj putj).2
    (Or.inr ⟨K0, Kj, k0, kj, put0, putj, h, idle_blindV a N VA K0 Kj k0 kj M0 Mj put0 putj⟩)

/-- the link that does nothing, in every slot, is a piece, if the demand is kept by subsets of slots
(`hH`) -/
theorem idle_pv {E : Type} [Field E] (a : LdStage E Unit) (N : ℕ) (VA : JV N a.J) (hH : VA.q.Her) :
    (a.idLink.loV N VA VA.tie VA.q).PV := by
  refine linkLoV_pv Unit _ _ a.idLink N VA VA.tie VA.q (LdStage.idLink_goodT a) (fun _ _ => rfl)
    (fun x y w _ _ h _ => h.2) ?_ hH
  intro J ρ Us h
  refine ⟨fun _ => trivial, ?_⟩
  have e : (fun j : J => a.idLink.R.need (ρ.slot j.1) (Us j)) = Us :=
    funext fun j =>
      (need_pure (fun x => some x) (ExtMap.id a.Ex) (ρ.slot j.1) (Us j)).trans
        (extId_src a.Ex _ (Us j))
  rw [e]
  exact h

section
variable (E : Type) [Field E] [Fintype E]

open Front in
theorem frontV_forgetLo : Spec.frontV_forgetLo E := by
  intro S E₀ Wp G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f g m back N W0 t₁ q t₂ t₃ q₃
  rw [cA_step, cA_split, cA_nil]
  unfold ldFrLo
  rw [ChainV.forget_snoc, ChainV.forget_snoc, ChainV.forget_one]
  rfl

open Front in
theorem frontV_forgetSh : Spec.frontV_forgetSh E := by
  intro S E₀ Wp G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f g m back N W0 t₁ q rd t₂ t₃ q₃
  rw [cA_step, cA_split, cA_nil]
  unfold ldFrSh
  rw [ChainV.forget_snoc, ChainV.forget_snoc, ChainV.forget_one]
  rfl

theorem frontV_lo : Spec.frontV_lo E := by
  intro D N W0 t₁ q t₂ B L t₃ q₃ Z VZ c₀ hD hL hHid hq hq₃ h2 h3 hB hF
  unfold ldFrLo
  refine (ChainV.okFromV_snoc c₀ _ _).2
    ⟨(ChainV.okFromV_snoc c₀ _ _).2
        ⟨(ChainV.okFromV_one c₀ _).2 (Or.inl (idle_pv D.src N ⟨W0, t₁, q⟩ hq)),
          Or.inr ⟨D.mask.localV W0 N, ?_, ?_⟩⟩,
      Or.inl (linkLoV_pv Unit _ _ L N ⟨W0, t₂, q⟩ t₃ q₃ hL hHid h3 hB hq₃)⟩
  · exact ldSplV_lo_pm E Unit D N ⟨W0, t₁, q⟩ t₂ hD h2 hq
  · rw [ChainV.append_one]
    exact idleV_fresh E D.src N ⟨W0, t₁, q⟩ Z VZ c₀ _ _ _ _ _ _ _ _ hF

theorem frontV_sh : Spec.frontV_sh E := by
  intro D N W0 t₁ q rd xp₀ t₂ B L t₃ q₃ Z VZ c₀ hD hL hHid hq hq₃ hrd h2 h3 hB hF
  unfold ldFrSh
  refine (ChainV.okFromV_snoc c₀ _ _).2
    ⟨(ChainV.okFromV_snoc c₀ _ _).2
        ⟨(ChainV.okFromV_one c₀ _).2 (Or.inl (idle_pv D.src N ⟨W0, t₁, q⟩ hq)),
          Or.inr ⟨(D.mask.tagPub xp₀).sharedV rd N, ?_, ?_⟩⟩,
      Or.inl (linkLoV_pv Unit _ _ L N ⟨W0, t₂, q⟩ t₃ q₃ hL hHid h3 hB hq₃)⟩
  · exact ldSplV_sh_pm E Unit D N ⟨W0, t₁, q⟩ rd xp₀ t₂ hD hrd h2 hq
  · rw [ChainV.append_one]
    exact idleV_fresh E D.src N ⟨W0, t₁, q⟩ Z VZ c₀ _ _ _ _ _ _ _ _ hF

end
end Cb
