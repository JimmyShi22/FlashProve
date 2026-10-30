-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecMinProofs.lean: the proofs of the statements of Cb/Gen/OodDecMin.lean (the decoder by a
constrained minimum).

The theorems are "ood_* : Cb.Spec.ood_*"; `Ood.exists_first_within` and `Ood.not_coll_of_not_clash`
are auxiliary.
-/
import Cb.Gen.OodDecMin
import Cb.Gen.OodDecProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

theorem ood_first_exists : Spec.ood_first_exists := by
  intro T U D Y dist rank view ev ρ y ⟨t0, h0⟩
  classical
  have hP : ∃ d, ∃ t, ev ρ (view t) = y ∧ dist t = d := ⟨dist t0, t0, h0, rfl⟩
  obtain ⟨t1, h1, hd1⟩ := Nat.find_spec hP
  have hQ : ∃ r, ∃ t, ev ρ (view t) = y ∧ dist t = Nat.find hP ∧ rank t = r :=
    ⟨rank t1, t1, h1, hd1, rfl⟩
  obtain ⟨t, ht, hdt, hrt⟩ := Nat.find_spec hQ
  refine ⟨t, ht, fun t' ht' => ?_⟩
  have hle : Nat.find hP ≤ dist t' := Nat.find_min' hP ⟨t', ht', rfl⟩
  rcases Nat.lt_or_ge (dist t) (dist t') with hlt | hge
  · exact Or.inl hlt
  · have heq : dist t' = Nat.find hP := by omega
    refine Or.inr ⟨by omega, ?_⟩
    rw [hrt]
    exact Nat.find_min' hQ ⟨t', ht', heq, rfl⟩

theorem ood_first_unique : Spec.ood_first_unique := by
  intro T U D Y dist rank view ev ρ y hr t t' h h'
  have a := h.2 t' h'.1
  have b := h'.2 t h.1
  exact hr (by omega)

/-- Auxiliary: if there is a candidate, some first minimizer is within the radius. -/
theorem Ood.exists_first_within {T U D Y : Type} (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y)
    (e : ℕ) (ρ : D) (y : Y) (u : U) (h : Cand (Within dist view e) ev ρ y u) :
    ∃ t, First dist rank view ev ρ y t ∧ dist t ≤ e := by
  obtain ⟨⟨t, hd, rfl⟩, hy⟩ := h
  obtain ⟨t0, h0⟩ := ood_first_exists T U D Y dist rank view ev ρ y ⟨t, hy⟩
  have := h0.2 t hy
  exact ⟨t0, h0, by omega⟩

theorem ood_decMin_iff : Spec.ood_decMin_iff := by
  intro T U D Y dist rank view ev e ρ y u hr
  unfold decMin
  by_cases h : ∃ t, First dist rank view ev ρ y t ∧ dist t ≤ e
  · rw [dif_pos h]
    constructor
    · intro h0
      exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, Option.some.inj h0⟩
    · rintro ⟨t, ht, _, rfl⟩
      exact congrArg (fun t => some (view t))
        (ood_first_unique T U D Y dist rank view ev ρ y hr _ _ h.choose_spec.1 ht)
  · rw [dif_neg h]
    exact ⟨(fun h0 => nomatch h0), fun ⟨t, ht, hd, _⟩ => absurd ⟨t, ht, hd⟩ h⟩

theorem ood_decMin_cand : Spec.ood_decMin_cand := by
  intro T U D Y dist rank view ev e ρ y u h0
  unfold decMin at h0
  by_cases h : ∃ t, First dist rank view ev ρ y t ∧ dist t ≤ e
  · rw [dif_pos h] at h0
    have hu : view h.choose = u := Option.some.inj h0
    exact ⟨⟨h.choose, h.choose_spec.2, hu⟩, by rw [← hu]; exact h.choose_spec.1.1⟩
  · rw [dif_neg h] at h0
    exact nomatch h0

theorem ood_decMin_none_iff : Spec.ood_decMin_none_iff := by
  intro T U D Y dist rank view ev e ρ y
  constructor
  · intro h0 u hu
    have h := exists_first_within dist rank view ev e ρ y u hu
    unfold decMin at h0
    rw [dif_pos h] at h0
    exact nomatch h0
  · intro h0
    cases hv : decMin dist rank view ev e ρ y with
    | none => rfl
    | some u => exact absurd (ood_decMin_cand T U D Y dist rank view ev e ρ y u hv) (h0 u)

theorem ood_one_cand : Spec.ood_one_cand := by
  intro U D Y Lst ev ρ y hc u u' hu hu'
  exact by_contra fun hne => hc ⟨u, u', hne, hu, hu'⟩

theorem ood_decMin_good : Spec.ood_decMin_good := by
  intro T U D Y dist rank view ev e ρ y hc u
  refine ⟨ood_decMin_cand T U D Y dist rank view ev e ρ y u, fun hu => ?_⟩
  cases hv : decMin dist rank view ev e ρ y with
  | none => exact absurd hu ((ood_decMin_none_iff T U D Y dist rank view ev e ρ y).mp hv u)
  | some u' =>
    exact congrArg some
      (ood_one_cand U D Y _ ev ρ y hc u' u
        (ood_decMin_cand T U D Y dist rank view ev e ρ y u' hv) hu)

theorem ood_decMin_pick : Spec.ood_decMin_pick := by
  intro T U D Y dist rank view ev e ρ y
  refine ⟨(ood_decMin_none_iff T U D Y dist rank view ev e ρ y).trans
      (ood_pick_none_iff U D Y _ ev ρ y).symm,
    fun hc => ?_⟩
  cases hv : pick (Within dist view e) ev ρ y with
  | one u =>
    exact (ood_decMin_good T U D Y dist rank view ev e ρ y hc u).mpr
      ((ood_pick_iff U D Y _ ev ρ y u).mp hv).1
  | none =>
    exact (ood_decMin_none_iff T U D Y dist rank view ev e ρ y).mpr
      ((ood_pick_none_iff U D Y _ ev ρ y).mp hv)
  | several => exact absurd ((ood_pick_several_iff U D Y _ ev ρ y).mp hv) hc

theorem ood_within_inList : Spec.ood_within_inList := by
  intro E ι κ R J _ _ _ G e view f
  rfl

/-- Auxiliary: no clash at the seed, no collision at any answer. -/
theorem Ood.not_coll_of_not_clash
    {U D Y : Type} {Lst : U → Prop} {ev : D → U → Y} {ρ : D} (h : ¬ Clash Lst ev ρ) (y : Y) :
    ¬ Coll Lst ev ρ y :=
  fun hc => h ((ood_clash_iff U D Y Lst ev ρ).mpr ⟨y, hc⟩)

theorem ood_decMinS_good : Spec.ood_decMinS_good := by
  intro E ι κ R J _ _ _ _ G e rank view Z f ρ hcl y u
  exact ood_decMin_good _ _ _ _ (fun M => cnt (Off G f M)) rank view Z.val e ρ y
    (not_coll_of_not_clash hcl y) u

theorem ood_decMinS_main : Spec.ood_decMinS_main := by
  intro E ι κ R J _ _ _ _ G e rank view Z f L hL hZ
  refine (cnt_mono fun ρ => ?_).trans (ood_cnt_clashS E ι κ R J G e view Z f L hL hZ)
  rintro ⟨y, M, hM, hy, hne⟩
  by_contra hcl
  exact hne ((ood_decMinS_good E ι κ R J G e rank view Z f ρ hcl y (view M)).mpr ⟨⟨M, hM, rfl⟩, hy⟩)

theorem ood_decMinS_near : Spec.ood_decMinS_near := by
  intro E ι κ R J _ _ _ _ G d e e' rank view Z f M hd he hee hM ρ
  have hall : ∀ u, InList G e view f u → u = view M := by
    rintro u ⟨M', h1, rfl⟩
    exact congrArg view (funext fun _ => DecodesTo.row_unique hd hee h1 hM rfl)
  refine (ood_decMin_good _ _ _ _ (fun M => cnt (Off G f M)) rank view Z.val e ρ _ ?_ (view M)).mpr
    ⟨⟨M, hM.mono he, rfl⟩, rfl⟩
  rintro ⟨u, u', hne, hu, hu'⟩
  exact hne ((hall u hu.1).trans (hall u' hu'.1).symm)

theorem ood_decMinS_mulVec : Spec.ood_decMinS_mulVec := by
  intro E ι κ R J _ _ _ _ G d e rank view Z M hd he ρ
  exact ood_decMinS_near E ι κ R J G d e 0 rank view Z _ M hd (Nat.zero_le e) (by omega)
    (decodesTo_mulVec G 0 M) ρ

theorem ood_decMinS_unique : Spec.ood_decMinS_unique := by
  intro E ι κ R J _ _ _ _ G d e rank view Z f ρ y u hd h2
  have hc : ¬ Coll (InList G e view f) Z.val ρ y := by
    rintro ⟨u₁, u₂, hne, ⟨⟨M₁, h1, rfl⟩, _⟩, ⟨⟨M₂, h2', rfl⟩, _⟩⟩
    exact hne (congrArg view (h1.unique hd h2 h2'))
  refine (ood_decMin_good _ _ _ _ (fun M => cnt (Off G f M))
    rank view Z.val e ρ y hc u).trans ⟨?_, ?_⟩
  · rintro ⟨⟨M, hM, hu⟩, hy⟩
    have hM' : DecodesTo G e f M := hM
    exact ⟨⟨M, hM'⟩, by rw [hM'.dec_eq hd h2]; exact hu, hy⟩
  · rintro ⟨hdec, hu, hy⟩
    exact ⟨⟨_, hdec.decodesTo_dec, hu⟩, hy⟩

end Cb
