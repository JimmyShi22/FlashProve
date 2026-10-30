-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscMaskProofs.lean: the proofs of the statements of Cb/Ld/LdPscMask.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdPscMask.lean):
  `rounds_cons`: round polynomials of a summand, and its sum.
  `psc_tr_law`, `psc_val_own`, `psc_mask_law`, `psc_sim_unif`: see their statements in
    Cb/Ld/LdPscMask.lean.
  `psc_sim_card`: the number of triples that pass the checks.
-/
import Cb.Ld.LdPscMask
import Cb.Ld.LdSumRun

set_option autoImplicit false

namespace Cb
open Prob

section Lemmas
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem HVar.phi_smul (v : HVar R) (a : R) (c : Fin (v.n + 1) → M) :
    v.phi (fun t => a • c t) = a • v.phi c := by
  unfold HVar.phi
  rw [← HVar.sum_smul]
  exact congrArg v.sum (funext fun x => hev_smul a c x)

theorem HCons.smul :
    ∀ (l : List (HVar R)) (a : R) {σ : M} {q : RIdx l → M} {γ : HPt l},
      HCons l σ q γ → HCons l (a • σ) (a • q) γ := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; trivial
  | cons v l ih =>
      intro a σ q γ h
      refine ⟨?_, ?_⟩
      · show v.phi (fun t => a • q (.inl t)) = _
        rw [HVar.phi_smul, h.1]
      · show HCons l (hev (fun t => a • q (.inl t)) γ.1) (a • fun i => q (.inr i)) γ.2
        rw [hev_smul]
        exact ih a h.2

theorem hMu_zero (l : List (HVar R)) : hMu l (0 : HIdx l → M) = 0 := by
  have h := hMu_add l (0 : HIdx l → M) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- Under `hOK`, `hu`, `hu'`: the law of (sum, round polynomials + u) does not depend on u. -/
theorem hide_law_one [Fintype M] (l : List (HVar R)) (hOK : ∀ v ∈ l, v.OK) (γ : HPt l) (σ : M)
    (u u' : RIdx l → M) (hu : HCons l σ u γ) (hu' : HCons l σ u' γ) :
    (unif (HIdx l → M)).map (fun W => (hMu l W, hTr l 0 W γ + u)) =
      (unif (HIdx l → M)).map fun W => (hMu l W, hTr l 0 W γ + u') := by
  have h0 : HCons l (0 + 0) (u - u') γ := by
    have := HCons.sub l hu hu'
    rwa [sub_self, ← add_zero (0 : M)] at this
  obtain ⟨i1, i2⟩ := hide_inv_right R M l hOK 0 0 (u - u') γ h0
  have e : (fun W : HIdx l → M => (hMu l W, hTr l 0 W γ + u))
      = (fun W => (hMu l W, hTr l 0 W γ + u')) ∘ Equiv.addRight (hInv l 0 0 (u - u') γ) := by
    funext W
    have ht := hTr_add l 0 0 W (hInv l 0 0 (u - u') γ) γ
    rw [add_zero] at ht
    show _ = (hMu l (W + hInv l 0 0 (u - u') γ), hTr l 0 (W + hInv l 0 0 (u - u') γ) γ + u')
    rw [hMu_add, ht, i1, i2, add_zero]
    congr 1
    abel
  rw [e, ← PMF.map_comp, map_unif_equiv (Equiv.addRight _)]

end Lemmas

theorem rounds_cons : Spec.rounds_cons := by
  intro R _ M _ _ l
  induction l with
  | nil => intro _ _ _ _; trivial
  | cons v l ih =>
      intro f q γ h
      refine ⟨?_, ?_⟩
      · show v.sum (hev fun t => q (.inl t)) = v.sum fun x => hSumAll l fun xs => f (x, xs)
        exact congrArg v.sum (funext h.1)
      · have h2 := ih (fun xs => f (γ.1, xs)) (fun i => q (.inr i)) γ.2 h.2
        rw [← h.1 γ.1] at h2
        exact h2

section Laws

/-- a function of a pair, the second part drawn first -/
theorem map_unif_pair_bind {Ω₁ Ω₂ Z : Type} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂]
    [Nonempty Ω₂] (f : Ω₂ → Ω₁ → Z) :
    (unif (Ω₁ × Ω₂)).map (fun s => f s.2 s.1) = (unif Ω₂).bind fun c => (unif Ω₁).map (f c) := by
  have h : unif (Ω₁ × Ω₂) = (unif (Ω₂ × Ω₁)).map Prod.swap :=
    (map_unif_equiv (Equiv.prodComm Ω₂ Ω₁)).symm
  rw [h, PMF.map_comp, unif_prod]
  unfold Prob.prod
  rw [PMF.map_bind]
  refine congrArg _ (funext fun c => ?_)
  rw [PMF.map_comp]
  rfl

/-- Two parts. If the first part has one law for every value of the second coin, and the second part
is uniform, the pair has the law of "that law, and an independent uniform value". -/
theorem psc_law_two {Ω₁ Ω₂ T Y : Type} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    [Fintype Y] [Nonempty Y] (g : Ω₂ → Ω₁ → T) (g' : Ω₁ → T) (v : Ω₂ → Y)
    (h1 : ∀ c, (unif Ω₁).map (g c) = (unif Ω₁).map g') (h2 : (unif Ω₂).map v = unif Y) :
    (unif (Ω₁ × Ω₂)).map (fun s => (g s.2 s.1, v s.2)) =
      (unif (Ω₁ × Y)).map fun s => (g' s.1, s.2) := by
  rw [map_unif_pair_bind (fun c W => (g c W, v c)),
    map_unif_pair_bind (fun y W => (g' W, y)), ← h2, PMF.bind_map]
  refine congrArg _ (funext fun c => ?_)
  show (unif Ω₁).map ((fun t => (t, v c)) ∘ g c) = (unif Ω₁).map ((fun t => (t, v c)) ∘ g')
  rw [← PMF.map_comp, ← PMF.map_comp, h1]

end Laws

section Main
variable (E : Type) [Field E] [Fintype E]

theorem psc_tr_law : Spec.psc_tr_law E := by
  intro l hOK γ ε τ u₀ hu
  have h1 : HCons l (ε * τ) (ε • u₀) γ := HCons.smul l ε hu
  have h2 : HCons l (ε * τ) (hTr l (ε * τ) (0 : HIdx l → E) γ) γ := by
    have h := hide_cons E E l hOK (ε * τ) 0 γ
    rwa [hMu_zero, add_zero] at h
  rw [hide_law_one l hOK γ (ε * τ) _ _ h1 h2]
  refine congrArg (fun f => (unif (HIdx l → E)).map f) (funext fun W => ?_)
  have ht := hTr_add l 0 (ε * τ) W 0 γ
  rw [zero_add, add_zero] at ht
  rw [ht]

theorem psc_val_own : Spec.psc_val_own E := by
  intro A _ _ F β hβ
  refine map_unif_pi (fun a x => F a + β * x) fun a =>
    map_unif_of_bijective (Finite.injective_iff_bijective.1 ?_)
  intro x y h
  exact mul_left_cancel₀ hβ (add_left_cancel h)

theorem psc_mask_law : Spec.psc_mask_law E := by
  intro l hOK Cx A _ _ _ _ γ ε τ u v hu hv
  have h := psc_law_two (fun c W => (hMu l W, hTr l 0 W γ + ε • u c))
    (fun W => (hMu l W, hTr l (ε * τ) W γ)) v (fun c => psc_tr_law E l hOK γ ε τ (u c) (hu c)) hv
  have h' := congrArg (PMF.map fun t : (E × (RIdx l → E)) × (A → E) => (t.1.1, t.1.2, t.2)) h
  rw [PMF.map_comp, PMF.map_comp] at h'
  exact h'

omit [Fintype E] in
theorem psc_sim_unif : Spec.psc_sim_unif E := by
  intro l hOK A γ ε τ
  refine ⟨?_, fun p => ⟨fun hp => ?_, ?_⟩⟩
  · intro s s' h
    have h1 : hMu l s.1 = hMu l s'.1 := congrArg Prod.fst h
    have h2 : hTr l (ε * τ) s.1 γ = hTr l (ε * τ) s'.1 γ := congrArg (fun t => t.2.1) h
    have h3 : s.2 = s'.2 := congrArg (fun t => t.2.2) h
    refine Prod.ext ?_ h3
    rw [← hide_inv_left E E l (ε * τ) s.1 γ, h1, h2, hide_inv_left]
  · have hp' : HCons l (ε * τ + p.1) p.2.1 γ := by rw [add_comm]; exact hp
    obtain ⟨i1, i2⟩ := hide_inv_right E E l hOK (ε * τ) p.1 p.2.1 γ hp'
    exact ⟨(hInv l (ε * τ) p.1 p.2.1 γ, p.2.2), Prod.ext i1 (Prod.ext i2 rfl)⟩
  · rintro ⟨s, rfl⟩
    have h := hide_cons E E l hOK (ε * τ) s.1 γ
    rw [add_comm] at h
    exact h

theorem psc_sim_card : Spec.psc_sim_card E := by
  intro l hOK A _ _ γ ε τ
  obtain ⟨hi, hr⟩ := psc_sim_unif E l hOK A γ ε τ
  rw [cnt_congr hr]
  show Nat.card (Set.range (pscSimMsg (A := A) l γ ε τ)) = _
  rw [← Nat.card_congr (Equiv.ofInjective _ hi), Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fun, pow_add]

end Main
end Cb
