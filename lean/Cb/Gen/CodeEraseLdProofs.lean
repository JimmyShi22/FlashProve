-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeEraseLdProofs.lean: the proofs of the statements of Cb/Gen/CodeEraseLd.lean. Nothing is
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

The map w = (message, randomness) ↦ transform of the encoding of w (`LdCode.te`) is linear
(`C.Laws`), and by `C.Dist d` the image of a non-zero w is non-zero at d long positions or more. So
two w that fit the same long word on more than (number of positions) - d positions are equal
(`lde_unique`).
-/
import Cb.Gen.CodeEraseLd

set_option autoImplicit false

namespace Cb
open Prob

namespace LdCode
variable {E P : Type} [Field E] (C : LdCode E P)

/-- the transform of the encoding -/
def te (w : C.MR) : P → C.Aa → E := C.T (C.enc w.1 w.2)

variable {C}

theorem te_add (h : C.Laws) (w w' : C.MR) : C.te (w + w') = C.te w + C.te w' := by
  unfold te
  have h1 : C.enc (w + w').1 (w + w').2 = C.enc w.1 w.2 + C.enc w'.1 w'.2 := h.encLin.map_add w w'
  rw [h1, h.tLin.map_add]

theorem te_smul (h : C.Laws) (c : E) (w : C.MR) : C.te (c • w) = c • C.te w := by
  unfold te
  have h1 : C.enc (c • w).1 (c • w).2 = c • C.enc w.1 w.2 := h.encLin.map_smul c w
  rw [h1, h.tLin.map_smul]

theorem te_sub (h : C.Laws) (w w' : C.MR) : C.te (w - w') = C.te w - C.te w' := by
  have h1 : w - w' = w + (-1 : E) • w' := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h1, te_add h, te_smul h, neg_one_smul, sub_eq_add_neg]

omit [Field E] in
/-- erase? in terms of uniqueness alone -/
theorem erase_iff_of_unique [Fintype P] {d : ℕ} {S : Finset P} {g : P → C.Aa → E}
    (hu : Fintype.card P < S.card + d →
      ∀ w w' : C.MR, C.AgreesOn S g w → C.AgreesOn S g w' → w = w') (w : C.MR) :
    C.erase? d S g = some w ↔ Fintype.card P < S.card + d ∧ C.AgreesOn S g w := by
  constructor
  · intro h
    by_cases hc : Fintype.card P < S.card + d ∧ ∃ w, C.AgreesOn S g w
    · unfold erase? at h
      rw [dif_pos hc] at h
      exact ⟨hc.1, Option.some.inj h ▸ hc.2.choose_spec⟩
    · unfold erase? at h
      rw [dif_neg hc] at h
      cases h
  · rintro ⟨hS, hw⟩
    have hc : Fintype.card P < S.card + d ∧ ∃ w, C.AgreesOn S g w := ⟨hS, w, hw⟩
    unfold erase?
    rw [dif_pos hc]
    exact congrArg some (hu hS _ _ hc.2.choose_spec hw)

end LdCode

open LdCode

section
variable (E : Type) [Field E] (P : Type) [Fintype P]

omit [Field E] [Fintype P] in
theorem lde_onCode_iff : Spec.lde_onCode_iff E P := fun _ _ _ =>
  ⟨fun ⟨m, r, h⟩ => ⟨(m, r), h⟩, fun ⟨w, h⟩ => ⟨w.1, w.2, h⟩⟩

theorem lde_unique : Spec.lde_unique E P := by
  intro C d hL hd S hS g w w' h h'
  by_contra hne
  have h0 : ¬ ((w - w').1 = 0 ∧ (w - w').2 = 0) := fun hz =>
    hne (sub_eq_zero.mp (Prod.ext hz.1 hz.2))
  have h1 := hd (w - w').1 (w - w').2 h0
  have h2 := cnt_add_card_le (P := fun x => C.T (C.enc (w - w').1 (w - w').2) x ≠ 0) (S := S) (fun x hx hc => hc (by
    have h3 : C.T (C.enc (w - w').1 (w - w').2) = C.te w - C.te w' := te_sub hL w w'
    rw [h3, Pi.sub_apply]
    show C.T (C.enc w.1 w.2) x - C.T (C.enc w'.1 w'.2) x = 0
    rw [← h x hx, ← h' x hx, sub_self]))
  omega

theorem lde_erase_iff : Spec.lde_erase_iff E P := fun C d hL hd S g w =>
  erase_iff_of_unique (fun hS w w' => lde_unique E P C d hL hd S hS g w w') w

omit [Field E] in
theorem lde_erase_none_iff : Spec.lde_erase_none_iff E P := by
  intro C d S g
  rw [lde_onCode_iff E P C g S]
  by_cases hc : Fintype.card P < S.card + d ∧ ∃ w, C.AgreesOn S g w
  · unfold erase?
    rw [dif_pos hc]
    exact ⟨fun h => (by cases h), fun h => absurd hc h⟩
  · unfold erase?
    rw [dif_neg hc]
    exact ⟨fun _ => hc, fun _ => rfl⟩

theorem lde_eraseD : Spec.lde_eraseD E P := fun C d S g w h => by
  unfold eraseD
  rw [h, Option.getD_some]

theorem mem_agr' {E P : Type} [Field E] [Fintype P] (C : LdCode E P)
    (g : P → C.Aa → E) (w : C.MR) (x : P) :
    x ∈ C.agr g w ↔ g x = C.T (C.enc w.1 w.2) x := by
  simp only [LdCode.agr, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Field E] in
theorem lde_near_iff_agr : Spec.lde_near_iff_agr E P := by
  intro C e f w
  have h1 := cnt_add_cnt_not (fun x => C.T f x = C.T (C.enc w.1 w.2) x)
  have h2 : (C.agr (C.T f) w).card = cnt (fun x => C.T f x = C.T (C.enc w.1 w.2) x) := by
    classical
    unfold LdCode.agr
    convert (cnt_eq_card_filter (fun x => C.T f x = C.T (C.enc w.1 w.2) x)).symm
  have h3 : C.Near e f (C.enc w.1 w.2) ↔ cnt (fun x => ¬ C.T f x = C.T (C.enc w.1 w.2) x) ≤ e :=
    Iff.rfl
  rw [h3]
  omega

theorem lde_erase_agr : Spec.lde_erase_agr E P := by
  intro C d e hL hd he f w h
  have h1 := (lde_near_iff_agr E P C e f w).mp h
  exact (lde_erase_iff E P C d hL hd _ _ w).mpr ⟨by omega, fun x hx => (mem_agr' C _ w x).mp hx⟩

theorem lde_erase_near : Spec.lde_erase_near E P := by
  intro C d e hL hd S f w h hS
  have h1 := ((lde_erase_iff E P C d hL hd S _ w).mp h).2
  have h2 : S ⊆ C.agr (C.T f) w := fun x hx => (mem_agr' C _ w x).mpr (h1 x hx)
  have h3 := Finset.card_le_card h2
  exact (lde_near_iff_agr E P C e f w).mpr (by omega)

theorem lde_erase_anti : Spec.lde_erase_anti E P := by
  intro C d hL hd S S' g w hSS hl h
  exact (lde_erase_iff E P C d hL hd S g w).mpr
    ⟨hl, fun x hx => ((lde_erase_iff E P C d hL hd S' g w).mp h).2 x (hSS hx)⟩

theorem agreesOn_line {E P : Type} [Field E] {C : LdCode E P} (hL : C.Laws)
    {S : Finset P} {g₀ g₁ : P → C.Aa → E} {w₀ w₁ : C.MR} (c₀ c₁ : E)
    (h₀ : C.AgreesOn S g₀ w₀) (h₁ : C.AgreesOn S g₁ w₁) :
    C.AgreesOn S (c₀ • g₀ + c₁ • g₁) (c₀ • w₀ + c₁ • w₁) := by
  intro x hx
  have h : C.T (C.enc (c₀ • w₀ + c₁ • w₁).1 (c₀ • w₀ + c₁ • w₁).2) =
      c₀ • C.te w₀ + c₁ • C.te w₁ := by
    have := te_add hL (c₀ • w₀) (c₁ • w₁)
    rw [te_smul hL, te_smul hL] at this
    exact this
  rw [h, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    Pi.smul_apply, h₀ x hx, h₁ x hx]
  rfl

theorem lde_erase_line : Spec.lde_erase_line E P := by
  intro C d hL hd S g₀ g₁ w₀ w₁ c₀ c₁ h₀ h₁
  obtain ⟨hl, a₀⟩ := (lde_erase_iff E P C d hL hd S g₀ w₀).mp h₀
  obtain ⟨-, a₁⟩ := (lde_erase_iff E P C d hL hd S g₁ w₁).mp h₁
  exact (lde_erase_iff E P C d hL hd S _ _).mpr ⟨hl, agreesOn_line hL c₀ c₁ a₀ a₁⟩

theorem lde_mcaAt_iff_exc [Finite E] : Spec.lde_mcaAt_iff_exc E P := fun _ _ _ => Iff.rfl

theorem lde_mcaAt_fold [Finite E] : Spec.lde_mcaAt_fold E P := by
  intro C e bad hL h f₀ f₁
  refine (cnt_mono ?_).trans (h f₀ (f₁ - f₀))
  rintro θ ⟨S, hS, hl, hn⟩
  have hsub : C.T (f₁ - f₀) = C.T f₁ - C.T f₀ := hL.tLin.map_sub f₁ f₀
  refine ⟨S, hS, ?_, fun hb => hn ⟨hb.1, ?_⟩⟩
  · have e1 : C.T f₀ + θ • C.T (f₁ - f₀) = (1 - θ) • C.T f₀ + θ • C.T f₁ := by
      rw [hsub, smul_sub, sub_smul, one_smul]
      abel
    rw [e1]
    exact hl
  · obtain ⟨w₀, a₀⟩ := (lde_onCode_iff E P C _ S).mp hb.1
    obtain ⟨w', a'⟩ := (lde_onCode_iff E P C _ S).mp hb.2
    have h1 := agreesOn_line hL 1 1 a₀ a'
    have e2 : (1 : E) • C.T f₀ + (1 : E) • C.T (f₁ - f₀) = C.T f₁ := by
      rw [hsub, one_smul, one_smul]
      abel
    rw [e2] at h1
    exact (lde_onCode_iff E P C _ S).mpr ⟨_, h1⟩

theorem lde_ends_aux {E P : Type} [Field E] [Fintype P] {C : LdCode E P} {d e : ℕ} (hL : C.Laws)
    (hd : C.Dist d) (he : e < d) {S : Finset P} (hS : Fintype.card P ≤ S.card + e)
    {g₀ g₁ : P → C.Aa → E} (c₀ c₁ : E) (h : C.OnCode g₀ S ∧ C.OnCode g₁ S) :
    ∃ w₀ w₁,
      C.erase? d S g₀ = some w₀ ∧
      C.erase? d S g₁ = some w₁ ∧
      C.erase? d S (c₀ • g₀ + c₁ • g₁) = some (c₀ • w₀ + c₁ • w₁) := by
  obtain ⟨w₀, a₀⟩ := (lde_onCode_iff E P C _ S).mp h.1
  obtain ⟨w₁, a₁⟩ := (lde_onCode_iff E P C _ S).mp h.2
  have e₀ := (lde_erase_iff E P C d hL hd S g₀ w₀).mpr ⟨by omega, a₀⟩
  have e₁ := (lde_erase_iff E P C d hL hd S g₁ w₁).mpr ⟨by omega, a₁⟩
  exact ⟨w₀, w₁, e₀, e₁, lde_erase_line E P C d hL hd S g₀ g₁ w₀ w₁ c₀ c₁ e₀ e₁⟩

theorem lde_erase_ends : Spec.lde_erase_ends E P := by
  intro C d e hL hd he S hS f₀ f₁ θ hθ hl
  have hb : C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S := by_contra fun hc => hθ ⟨S, hS, hl, hc⟩
  have h := lde_ends_aux hL hd he hS 1 θ hb
  simpa only [one_smul] using h

theorem lde_erase_ends_fold : Spec.lde_erase_ends_fold E P := by
  intro C d e hL hd he S hS f₀ f₁ θ hθ hl
  have hb : C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S := by_contra fun hc => hθ ⟨S, hS, hl, hc⟩
  exact lde_ends_aux hL hd he hS (1 - θ) θ hb

theorem lde_erase_il : Spec.lde_erase_il E P := by
  intro C d hL hd R _ _ S hS g w
  have key : ∀ w : (C.il R).MR, (C.il R).AgreesOn S g w ↔
      ∀ i, C.AgreesOn S (fun x α => g x (i, α)) (fun j => w.1 (i, j), fun q => w.2 (i, q)) := by
    intro w
    constructor
    · intro h i x hx
      funext α
      exact congrFun (h x hx) (i, α)
    · intro h x hx
      funext α
      exact congrFun (h α.1 x hx) α.2
  have hu : Fintype.card P < S.card + d →
      ∀ w w' : (C.il R).MR, (C.il R).AgreesOn S g w → (C.il R).AgreesOn S g w' → w = w' := by
    intro _ w w' h h'
    have h1 : ∀ i, ((fun j => w.1 (i, j), fun q => w.2 (i, q)) : C.MR) =
        (fun j => w'.1 (i, j), fun q => w'.2 (i, q)) := fun i =>
      lde_unique E P C d hL hd S hS _ _ _ ((key w).mp h i) ((key w').mp h' i)
    refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
    · exact congrFun (congrArg Prod.fst (h1 n.1)) n.2
    · exact congrFun (congrArg Prod.snd (h1 n.1)) n.2
  rw [erase_iff_of_unique hu w, key w]
  exact ⟨fun h i => (lde_erase_iff E P C d hL hd S _ _).mpr ⟨hS, h.2 i⟩,
    fun h => ⟨hS, fun i => ((lde_erase_iff E P C d hL hd S _ _).mp (h i)).2⟩⟩

theorem lde_erase_pair : Spec.lde_erase_pair E P := by
  intro C₁ C₂ d hL₁ hd₁ hL₂ hd₂ S hS g w
  have key : ∀ w : (C₁.pair C₂).MR, (C₁.pair C₂).AgreesOn S g w ↔
      C₁.AgreesOn S (fun x α => g x (.inl α)) (fun j => w.1 (.inl j), fun q => w.2 (.inl q)) ∧
      C₂.AgreesOn S (fun x α => g x (.inr α)) (fun j => w.1 (.inr j), fun q => w.2 (.inr q)) := by
    intro w
    constructor
    · intro h
      exact ⟨fun x hx => funext fun α => congrFun (h x hx) (.inl α),
        fun x hx => funext fun α => congrFun (h x hx) (.inr α)⟩
    · rintro ⟨h₁, h₂⟩ x hx
      funext α
      cases α with
      | inl α => exact congrFun (h₁ x hx) α
      | inr α => exact congrFun (h₂ x hx) α
  have hu : Fintype.card P < S.card + d →
      ∀ w w' : (C₁.pair C₂).MR,
        (C₁.pair C₂).AgreesOn S g w → (C₁.pair C₂).AgreesOn S g w' → w = w' := by
    intro _ w w' h h'
    have h1 := lde_unique E P C₁ d hL₁ hd₁ S hS _ _ _ ((key w).mp h).1 ((key w').mp h').1
    have h2 := lde_unique E P C₂ d hL₂ hd₂ S hS _ _ _ ((key w).mp h).2 ((key w').mp h').2
    refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
    · cases n with
      | inl j => exact congrFun (congrArg Prod.fst h1) j
      | inr j => exact congrFun (congrArg Prod.fst h2) j
    · cases n with
      | inl q => exact congrFun (congrArg Prod.snd h1) q
      | inr q => exact congrFun (congrArg Prod.snd h2) q
  rw [erase_iff_of_unique hu w, key w]
  exact ⟨fun h =>
      ⟨(lde_erase_iff E P C₁ d hL₁ hd₁ S _ _).mpr ⟨hS, h.2.1⟩,
        (lde_erase_iff E P C₂ d hL₂ hd₂ S _ _).mpr ⟨hS, h.2.2⟩⟩,
    fun h =>
      ⟨hS, ((lde_erase_iff E P C₁ d hL₁ hd₁ S _ _).mp h.1).2,
        ((lde_erase_iff E P C₂ d hL₂ hd₂ S _ _).mp h.2).2⟩⟩

end
end Cb
