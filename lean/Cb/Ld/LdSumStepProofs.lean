-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStepProofs.lean: the proofs of the statements of Cb/Ld/LdSumStep.lean (one round of a
fold beyond unique decoding: knowledge soundness on words). Nothing is assumed beyond the hypotheses
of the statements and whatever the arguments hold as proofs.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
Below, f, γ, w', e, κ are those of `Spec.lds_back` and `Spec.lds_round`.

The backward step. Let S be the set of long positions at which the fold agrees with the encoding of
w'; it omits at most e positions. On S the point (1 - γ) lo f + γ hi f of the line through the two
halves is on the code. As γ is not exceptional, both halves are on the code on S, so erasure
correction returns w₀ and w₁, and the point has the pair (1 - γ) w₀ + γ w₁ (`lde_erase_ends_fold`).
But w' also fits the point on S, and S is large: the two are equal. The pairs w₀, w₁ fit the halves
of one word on a large set, so they are the halves of w = join w₀ w₁. On S both halves of f are read
as those of the encoding of w, so f is read as that encoding.
The round. A value γ at which some witness after the round is not taken to a witness before it is
exceptional, or else w = back .. w' is a member of the list around f that folds to w'; it is no
witness, so its claim before the round is false; its claim after the round holds: γ is one of the at
most κ values that this member spoils.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumStep

set_option autoImplicit false

namespace Cb
open Prob LdCode

theorem t_fold {E P : Type} [Field E] {D D' : LdCode E P} (H : Halving D D')
    (hL : D'.Laws) (γ : E) (f : D.Word) :
    D'.T (H.fold γ f) = (1 - γ) • D'.T (H.lo f) + γ • D'.T (H.hi f) := by
  unfold Halving.fold
  rw [hL.tLin.map_add, hL.tLin.map_smul, hL.tLin.map_smul]

section
variable (E : Type) [Field E] (P : Type) [Fintype P]

theorem lds_back : Spec.lds_back E P := by
  intro D D' H d e hL hd hH he f γ hγ w' hw'
  have hS := (lde_near_iff_agr E P D' e (H.fold γ f) w').mp hw'
  have hag : D'.AgreesOn (D'.agr (D'.T (H.fold γ f)) w') (D'.T (H.fold γ f)) w' := fun x hx =>
    (mem_agr' D' _ w' x).mp hx
  have hb : H.back d γ f w' = H.join (D'.eraseD d (D'.agr (D'.T (H.fold γ f)) w') (D'.T (H.lo f)))
      (D'.eraseD d (D'.agr (D'.T (H.fold γ f)) w') (D'.T (H.hi f))) := rfl
  rw [hb]
  generalize D'.agr (D'.T (H.fold γ f)) w' = S at hS hag
  rw [t_fold H hL γ f] at hag
  have hon : D'.OnCode ((1 - γ) • D'.T (H.lo f) + γ • D'.T (H.hi f)) S :=
    (lde_onCode_iff E P D' _ S).mpr ⟨w', hag⟩
  obtain ⟨w₀, w₁, h₀, h₁, hp⟩ :=
    lde_erase_ends_fold E P D' d e hL hd he S hS (H.lo f) (H.hi f) γ hγ hon
  have hlarge : Fintype.card P < S.card + d := by omega
  have hw : (1 - γ) • w₀ + γ • w₁ = w' :=
    lde_unique E P D' d hL hd S hlarge _ _ _ ((lde_erase_iff E P D' d hL hd S _ _).mp hp).2 hag
  have a₀ := ((lde_erase_iff E P D' d hL hd S _ _).mp h₀).2
  have a₁ := ((lde_erase_iff E P D' d hL hd S _ _).mp h₁).2
  rw [lde_eraseD E P D' d S _ w₀ h₀, lde_eraseD E P D' d S _ w₁ h₁]
  have hfit := hH.fit f S w₀ w₁ hlarge a₀ a₁
  have hlo := hH.lo_join w₀ w₁ hfit
  have hhi := hH.hi_join w₀ w₁ hfit
  refine ⟨?_, ?_⟩
  · have h2 := cnt_add_card_le (P := fun x => D.T f x ≠ D.T (D.enc (H.join w₀ w₁).1 (H.join w₀ w₁).2) x) (S := S) (fun x hx hc => hc (by
      rw [hH.t_iff, hH.enc_lo, hH.enc_hi, hlo, hhi]
      exact ⟨a₀ x hx, a₁ x hx⟩))
    unfold LdCode.Near
    omega
  · unfold Halving.foldW
    rw [hlo, hhi]
    exact hw

omit [Field E] [Fintype P] in
theorem lds_cnt_list : Spec.lds_cnt_list := by
  intro α β _ _ Pm Q L κ hL hQ
  classical
  cases nonempty_fintype α
  cases nonempty_fintype β
  have h1 : cnt (fun a => ∃ b, Pm b ∧ Q b a) ≤ cnt (fun a => ∃ b ∈ Finset.univ.filter Pm, Q b a) :=
    cnt_mono fun a ⟨b, hb, hq⟩ => ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ b, hb⟩, hq⟩
  refine h1.trans ((cnt_exists_mem_le _ _).trans ?_)
  rw [cnt_eq_card_filter Pm] at hL
  calc ∑ i ∈ Finset.univ.filter Pm, cnt (Q i) ≤ ∑ _i ∈ Finset.univ.filter Pm, κ :=
        Finset.sum_le_sum fun i hi => hQ i (Finset.mem_filter.1 hi).2
    _ = (Finset.univ.filter Pm).card * κ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ L * κ := Nat.mul_le_mul_right κ hL

theorem lds_round [Finite E] : Spec.lds_round E P := by
  intro D D' H d e L bad κ hL hd hH he hList Φ Φ' hκ f hbad
  cases nonempty_fintype E
  have h1 : cnt (fun γ => ∃ w : D.MR, (D.Near e f (D.enc w.1 w.2) ∧ ¬ Φ w) ∧ Φ' γ (H.foldW γ w)) ≤
      L * κ :=
    lds_cnt_list E D.MR (fun w => D.Near e f (D.enc w.1 w.2) ∧ ¬ Φ w)
      (fun w γ => Φ' γ (H.foldW γ w)) L κ
      ((cnt_mono fun w hw => hw.1).trans (hList f)) fun w hw => hκ w hw.2
  refine le_trans (cnt_le_add fun γ hγ => ?_) (Nat.add_le_add hbad h1)
  obtain ⟨w', ⟨hn, hc⟩, hnot⟩ := hγ
  by_cases hex : H.Exc e f γ
  · exact Or.inl hex
  · obtain ⟨hnear, hfold⟩ := lds_back E P D D' H d e hL hd hH he f γ hex w' hn
    refine Or.inr ⟨H.back d γ f w', ⟨hnear, fun hΦ => hnot ⟨hnear, hΦ⟩⟩, ?_⟩
    rw [hfold]
    exact hc

omit [Fintype P] in
theorem lds_poly [Finite E] : Spec.lds_poly E := by
  intro d p q hp hq hne
  have hpq : p ≠ q := fun h => hne (by rw [h])
  exact Alg.count_eval_eq_le hpq (Nat.le_sub_one_of_lt hp) (Nat.le_sub_one_of_lt hq)

omit [Field E] in
theorem lds_il_laws : Spec.lds_il_laws E P := by
  intro C R R' _ _ _ _ ρ d
  refine ⟨fun _ => rfl, fun _ => rfl, fun f g x => ?_, fun w₀ w₁ _ => ?_,
    fun w₀ w₁ _ => ?_, fun _ _ _ _ _ _ _ => trivial⟩
  · constructor
    · intro h
      exact ⟨funext fun α => congrFun h (ρ (false, α.1), α.2),
        funext fun α => congrFun h (ρ (true, α.1), α.2)⟩
    · rintro ⟨h₀, h₁⟩
      funext α
      obtain ⟨⟨b, i⟩, hi⟩ := ρ.surjective α.1
      have hα : α = (ρ (b, i), α.2) := Prod.ext hi.symm rfl
      rw [hα]
      cases b
      · exact congrFun h₀ (i, α.2)
      · exact congrFun h₁ (i, α.2)
  · refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
    · show cond (ρ.symm (ρ (false, j.1))).1 _ _ = _
      rw [Equiv.symm_apply_apply]
      rfl
    · show cond (ρ.symm (ρ (false, q.1))).1 _ _ = _
      rw [Equiv.symm_apply_apply]
      rfl
  · refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
    · show cond (ρ.symm (ρ (true, j.1))).1 _ _ = _
      rw [Equiv.symm_apply_apply]
      rfl
    · show cond (ρ.symm (ρ (true, q.1))).1 _ _ = _
      rw [Equiv.symm_apply_apply]
      rfl

/-- What is read of a word of a pair at a long position: what is read of its two sides. -/
theorem t_pair_eq_iff {E P : Type} {C₁ C₂ : LdCode E P} (f g : (C₁.pair C₂).Word) (x : P) :
    (C₁.pair C₂).T f x = (C₁.pair C₂).T g x ↔
    C₁.T (fstW f) x = C₁.T (fstW g) x ∧ C₂.T (sndW f) x = C₂.T (sndW g) x := by
  constructor
  · intro h
    exact ⟨funext fun α => congrFun h (.inl α), funext fun α => congrFun h (.inr α)⟩
  · rintro ⟨h₁, h₂⟩
    funext α
    cases α with
    | inl α => exact congrFun h₁ α
    | inr α => exact congrFun h₂ α

theorem mkM_fst_snd {E P : Type} {C₁ C₂ : LdCode E P} (w : (C₁.pair C₂).MR) :
    mkM (fstM w) (sndM w) = w := by
  refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
  · cases j <;> rfl
  · cases q <;> rfl

theorem agreesOn_pair_iff {E P : Type} {C₁ C₂ : LdCode E P} (S : Finset P)
    (g : P → (C₁.pair C₂).Aa → E) (w : (C₁.pair C₂).MR) :
    (C₁.pair C₂).AgreesOn S g w ↔
    C₁.AgreesOn S (fun x α => g x (.inl α)) (fstM w) ∧
    C₂.AgreesOn S (fun x α => g x (.inr α)) (sndM w) := by
  constructor
  · intro h
    exact ⟨fun x hx => funext fun α => congrFun (h x hx) (.inl α),
      fun x hx => funext fun α => congrFun (h x hx) (.inr α)⟩
  · rintro ⟨h₁, h₂⟩ x hx
    funext α
    cases α with
    | inl α => exact congrFun (h₁ x hx) α
    | inr α => exact congrFun (h₂ x hx) α

theorem onCode_pair_iff {E P : Type} {C₁ C₂ : LdCode E P}
    (S : Finset P) (g : P → (C₁.pair C₂).Aa → E) :
    (C₁.pair C₂).OnCode g S ↔
    C₁.OnCode (fun x α => g x (.inl α)) S ∧ C₂.OnCode (fun x α => g x (.inr α)) S := by
  rw [lde_onCode_iff, lde_onCode_iff, lde_onCode_iff]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨⟨_, ((agreesOn_pair_iff S g w).mp hw).1⟩, ⟨_, ((agreesOn_pair_iff S g w).mp hw).2⟩⟩
  · rintro ⟨⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩
    exact ⟨mkM w₁ w₂, (agreesOn_pair_iff S g (mkM w₁ w₂)).mpr ⟨h₁, h₂⟩⟩

omit [Field E] in
theorem lds_pair_laws : Spec.lds_pair_laws E P := by
  intro D₁ D₁' D₂ D₂' H₁ H₂ d h₁ h₂
  refine ⟨fun w => ?_, fun w => ?_, fun f g x => ?_, fun w₀ w₁ hf => ?_,
    fun w₀ w₁ hf => ?_, fun f S w₀ w₁ hS a₀ a₁ => ?_⟩
  · funext x α
    cases α with
    | inl α => exact congrFun (congrFun (h₁.enc_lo (fstM w)) x) α
    | inr α => exact congrFun (congrFun (h₂.enc_lo (sndM w)) x) α
  · funext x α
    cases α with
    | inl α => exact congrFun (congrFun (h₁.enc_hi (fstM w)) x) α
    | inr α => exact congrFun (congrFun (h₂.enc_hi (sndM w)) x) α
  · rw [t_pair_eq_iff, t_pair_eq_iff, t_pair_eq_iff, h₁.t_iff, h₂.t_iff]
    exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨b, d⟩⟩, fun ⟨⟨a, c⟩, ⟨b, d⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩⟩
  · show mkM (H₁.loW (H₁.join (fstM w₀) (fstM w₁))) (H₂.loW (H₂.join (sndM w₀) (sndM w₁))) = w₀
    rw [h₁.lo_join _ _ hf.1, h₂.lo_join _ _ hf.2, mkM_fst_snd]
  · show mkM (H₁.hiW (H₁.join (fstM w₀) (fstM w₁))) (H₂.hiW (H₂.join (sndM w₀) (sndM w₁))) = w₁
    rw [h₁.hi_join _ _ hf.1, h₂.hi_join _ _ hf.2, mkM_fst_snd]
  · have b₀ := (agreesOn_pair_iff S _ w₀).mp a₀
    have b₁ := (agreesOn_pair_iff S _ w₁).mp a₁
    exact ⟨h₁.fit (fstW f) S _ _ hS b₀.1 b₁.1, h₂.fit (sndW f) S _ _ hS b₀.2 b₁.2⟩

theorem lds_idle_laws : Spec.lds_idle_laws E P := fun Z d hL hd =>
  ⟨fun _ => rfl, fun _ => rfl,
    fun _ _ _ => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩,
    fun _ _ _ => rfl, fun _ _ h => h,
    fun _ S w₀ w₁ hS a₀ a₁ => lde_unique E P Z d hL hd S hS _ w₀ w₁ a₀ a₁⟩

theorem lds_exc_pair : Spec.lds_exc_pair E P := by
  intro D₁ D₁' D₂ D₂' H₁ H₂ e f γ
  rintro ⟨S, hS, hl, hn⟩
  have hl' := (onCode_pair_iff S _).mp hl
  by_contra hno
  have k₁ : D₁'.OnCode (D₁'.T (H₁.lo (fstW f))) S ∧ D₁'.OnCode (D₁'.T (H₁.hi (fstW f))) S :=
    by_contra fun hc => hno (Or.inl ⟨S, hS, hl'.1, hc⟩)
  have k₂ : D₂'.OnCode (D₂'.T (H₂.lo (sndW f))) S ∧ D₂'.OnCode (D₂'.T (H₂.hi (sndW f))) S :=
    by_contra fun hc => hno (Or.inr ⟨S, hS, hl'.2, hc⟩)
  exact hn ⟨(onCode_pair_iff S _).mpr ⟨k₁.1, k₂.1⟩, (onCode_pair_iff S _).mpr ⟨k₁.2, k₂.2⟩⟩

theorem lds_exc_idle : Spec.lds_exc_idle E P := by
  intro Z e f γ
  rintro ⟨S, _, hl, hn⟩
  have e1 : (1 - γ) • Z.T f + γ • Z.T f = Z.T f := by rw [← add_smul, sub_add_cancel, one_smul]
  have hl' : Z.OnCode ((1 - γ) • Z.T f + γ • Z.T f) S := hl
  rw [e1] at hl'
  exact hn ⟨hl', hl'⟩

theorem lds_exc_cnt [Finite E] : Spec.lds_exc_cnt E P := fun _ D' H e bad hL h f =>
  lde_mcaAt_fold E P D' e bad hL h (H.lo f) (H.hi f)

omit [Field E] in
theorem lds_coeff [Finite E] : Spec.lds_coeff E P := by
  intro D e L κ hList Φ Φ' hκ f
  refine le_trans (cnt_mono ?_)
    (lds_cnt_list E D.MR (fun w => D.Near e f (D.enc w.1 w.2) ∧ ¬ Φ w) (fun w ε => Φ' ε w) L κ
      ((cnt_mono fun w hw => hw.1).trans (hList f)) fun w hw => hκ w hw.2)
  rintro ε ⟨w, ⟨hn, hc⟩, hnot⟩
  exact ⟨w, ⟨hn, hnot⟩, hc⟩

omit [Fintype P] in
theorem lds_affine [Finite E] : Spec.lds_affine E := by
  intro a b ha
  cases nonempty_fintype E
  refine cnt_le_one fun x y hx hy => ?_
  have h : (x - y) * a = 0 := by linear_combination hx - hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right ha)

end
end Cb
