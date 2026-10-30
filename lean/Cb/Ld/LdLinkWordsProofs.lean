-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinkWordsProofs.lean: the proofs of the statements of Cb/Ld/LdLinkWords.lean, on the link
between two encoded indices: completeness (`ldLk_complete`), the counts of bad values of γ, of the
locations and of φ (`ldLk_cnt_eq`, `ldLk_cnt_gam`, `ldLk_cnt_loc`, `ldLk_cnt_phi`), the backward
steps (`ldLk_back_gam`, `ldLk_back_phi`).

Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. What the statements say, with their hypotheses, and what they do not say:
Cb/Ld/LdLinkWords.lean.
-/
import Cb.Ld.LdLinkWords
import Cb.Ld.LdFoldEqProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

section
variable {E ι κ J Λ : Type} [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Λ]

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldLk_complete : Spec.ldLk_complete E ι κ J Λ := by
  intro D M₀ M₁ γ φ h
  have h1 : D.layV (foldAll γ M₀) = D.layV (foldAll γ M₁) := by
    funext a
    unfold LdLkW.layV
    rw [D.X.msg_foldAll, D.X.msg_foldAll]
    unfold foldV
    exact Finset.sum_congr rfl fun r _ => by rw [h r a]
  refine ⟨h1, ?_⟩
  unfold LdLkW.EqRow
  rw [h1]
  simp

omit [Fintype Λ] in
theorem ldLk_back_gam : Spec.ldLk_back_gam E ι κ J Λ := by
  intro D f₀ f₁ rec₀ rec₁ e₀ e₁ γ u₀ u₁ hb hn₀ hr₀ hn₁ hr₁ hl
  have hw₀ : ¬ D.X.Wrong f₀ rec₀ γ u₀ := fun h => hb (Or.inl ⟨u₀, hn₀, hr₀, h⟩)
  have hw₁ : ¬ D.X.Wrong f₁ rec₁ γ u₁ := fun h => hb (Or.inr (Or.inl ⟨u₁, hn₁, hr₁, h⟩))
  unfold LdIx.Wrong at hw₀ hw₁
  push Not at hw₀ hw₁
  obtain ⟨U₀, hU₀, hm₀⟩ := hw₀
  obtain ⟨U₁, hU₁, hm₁⟩ := hw₁
  refine ⟨U₀, U₁, hU₀, hU₁, ?_⟩
  by_contra hne
  refine hb (Or.inr (Or.inr ⟨U₀, U₁, hU₀, hU₁, hne, fun a => ?_⟩))
  rw [← hm₀, ← hm₁]
  exact congrFun hl a

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldLk_back_phi : Spec.ldLk_back_phi E ι κ J Λ := fun _ _ _ _ hb hr => by
  by_contra hne
  exact hb ⟨hne, hr⟩

omit [Fintype J] [Fintype Λ] in
theorem ldLk_cnt_loc : Spec.ldLk_cnt_loc E ι κ J Λ := by
  intro D t₀ t₁ e₀ e₁ w₀ w₁ u₀ u₁
  by_cases h₀ : D.X.NearW e₀ w₀ u₀
  · by_cases h₁ : D.X.NearW e₁ w₁ u₁
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro Q ⟨h | h, -⟩
        · exact h h₀
        · exact h h₁
    · refine le_trans ?_ (le_max_right _ _)
      refine le_trans
        (cnt_mono (Q := fun Q : (Fin t₀ → ι) × (Fin t₁ → ι) => D.ColW w₁ u₁ Q.2) fun Q hQ => hQ.2.2)
        ?_
      rw [cnt_snd (C := Fin t₀ → ι) (D.ColW (t := t₁) w₁ u₁), Fintype.card_fun, Fintype.card_fin]
      exact Nat.mul_le_mul_left _ (D.X.cnt_far_lists t₁ h₁)
  · refine le_trans ?_ (le_max_left _ _)
    refine le_trans
      (cnt_mono (Q := fun Q : (Fin t₀ → ι) × (Fin t₁ → ι) => D.ColW w₀ u₀ Q.1) fun Q hQ => hQ.2.1)
      ?_
    rw [cnt_fst (D := Fin t₁ → ι) (D.ColW (t := t₀) w₀ u₀), Fintype.card_fun, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (D.X.cnt_far_lists t₀ h₀)

variable [Fintype E]

omit [Fintype ι] [Fintype κ] [Fintype J] [Fintype Λ] in
theorem ldLk_cnt_eq : Spec.ldLk_cnt_eq E ι κ J Λ := by
  intro D U₀ U₁
  unfold LdLkW.BadEq
  refine cnt_and_le fun hne => ?_
  unfold LdLkW.SameOn at hne
  push Not at hne
  obtain ⟨r, a, hra⟩ := hne
  have h := Alg.count_mle_eq_le (fun r => U₀ (r, D.lay a))
    (fun r => U₁ (r, D.lay a)) fun h0 => hra (congrFun h0 r)
  rw [Fintype.card_fin] at h
  exact (cnt_mono fun γ hγ => hγ a).trans h

omit [Fintype Λ] in
theorem ldLk_cnt_gam : Spec.ldLk_cnt_gam E ι κ J Λ := by
  intro D f₀ f₁ rec₀ rec₁ e₀ e₁ ε₀ ε₁ h₀ h₁
  unfold LdLkW.BadGam
  refine (cnt_or_le _ _).trans ?_
  rw [Nat.add_assoc]
  refine Nat.add_le_add h₀ ((cnt_or_le _ _).trans (Nat.add_le_add h₁ ?_))
  refine (cnt_mono
    (Q := fun γ =>
        ∃ U₀, D.X.dec f₀ rec₀ = some U₀ ∧ ∃ U₁, D.X.dec f₁ rec₁ = some U₁ ∧ D.BadEq U₀ U₁ γ)
    fun γ ⟨U₀, U₁, h0, h1, hb⟩ => ⟨U₀, h0, U₁, h1, hb⟩).trans ?_
  refine cnt_exists_unique_le (P := fun U₀ => D.X.dec f₀ rec₀ = some U₀)
    (fun _ _ hb hb' => Option.some.inj (hb.symm.trans hb')) fun U₀ _ => ?_
  exact cnt_exists_unique_le (P := fun U₁ => D.X.dec f₁ rec₁ = some U₁)
    (fun _ _ hb hb' => Option.some.inj (hb.symm.trans hb')) fun U₁ _ => ldLk_cnt_eq D U₀ U₁

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldLk_cnt_phi : Spec.ldLk_cnt_phi E ι κ J Λ := by
  intro D u₀ u₁ hpl
  unfold LdLkW.BadPhi LdLkW.EqRow
  refine cnt_and_le fun hne => ?_
  have h := Alg.count_mle_zero_of_injective D.pl hpl (D.layV u₀ - D.layV u₁) (sub_ne_zero.mpr hne)
  rw [Fintype.card_fin] at h
  exact h

end
end Cb
