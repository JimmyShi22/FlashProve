-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBaseWordsProofs.lean: proofs of the statements of Cb/Ld/LdBaseWords.lean on the base case
(the agreement bound is in Cb/Ld/LdBaseThird.lean).

Every "Spec.name" there, but for `Spec.ldw_third` and `Spec.ldw_third_fold`, is "theorem name" here.
Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. What the statements say, and the limits: the head of Cb/Ld/LdBaseWords.lean.

Main names (statements and hypotheses: Cb/Ld/LdBaseWords.lean):
  `ldw_cnt_bad1`, `ldw_cnt_bad2`: the first error; the second error.
  `ldw_back`: the backward step.
  `ldw_unique`: below the distance, no choice of the corrected word.
  `ldw_complete`: completeness.
  `ldw_law`: see its statement in Cb/Ld/LdBaseWords.lean.
-/
import Cb.Ld.LdBaseWords
import Blocks.Decode

set_option autoImplicit false

namespace Cb
open Prob

/-- Union bound over a list: if each member of a list spoils at most k values, the list spoils at
most (its size) · k. -/
theorem ldw_cnt_list {α β : Type} [Fintype α] [Finite β] {P : β → Prop} {Q : β → α → Prop}
    {k : ℕ} (hQ : ∀ b, P b → cnt (Q b) ≤ k) :
    cnt (fun a => ∃ b, P b ∧ Q b a) ≤ cnt P * k := by
  classical
  cases nonempty_fintype β
  have h1 : cnt (fun a => ∃ b, P b ∧ Q b a) ≤ cnt (fun a => ∃ b ∈ Finset.univ.filter P, Q b a) :=
    cnt_mono fun a ⟨b, hb, hq⟩ => ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ b, hb⟩, hq⟩
  refine h1.trans ((cnt_exists_mem_le _ _).trans ?_)
  rw [cnt_eq_card_filter P]
  calc
    ∑ i ∈ Finset.univ.filter P, cnt (Q i) ≤ ∑ _i ∈ Finset.univ.filter P, k :=
      Finset.sum_le_sum fun i hi => hQ i (Finset.mem_filter.1 hi).2
    _ = (Finset.univ.filter P).card * k := by rw [Finset.sum_const, smul_eq_mul]

section
variable {W Y P : Type} [Fintype P] {cw : W → P → Y}

theorem mem_ldwAgree {f : P → Y} {M : W} {x : P} : x ∈ ldwAgree cw f M ↔ f x = cw M x := by
  classical
  unfold ldwAgree
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

/-- Agreement on a set that misses at most e positions is nearness at the radius e. -/
theorem ldwNear_of_agree {e : ℕ} {f : P → Y} {M : W} {S : Finset P}
    (hS : Fintype.card P ≤ S.card + e) (h : ∀ x ∈ S, f x = cw M x) : LdwNear cw e f M := by
  have h1 := cnt_add_card_le (P := fun x => f x ≠ cw M x) (S := S) fun x hx hn => hn (h x hx)
  unfold LdwNear
  omega

/-- Nearness at the radius e: the largest agreement set misses at most e positions. -/
theorem LdwNear.card_agree {e : ℕ} {f : P → Y} {M : W} (h : LdwNear cw e f M) :
    Fintype.card P ≤ (ldwAgree cw f M).card + e := by
  classical
  have h1 := cnt_add_cnt_not (fun x => f x ≠ cw M x)
  have h2 : cnt (fun x => ¬ f x ≠ cw M x) = (ldwAgree cw f M).card := by
    rw [cnt_eq_card_filter]
    unfold ldwAgree
    congr 1
    ext x
    simp
  unfold LdwNear at h
  omega

end

theorem ldw_cnt_bad1 : Spec.ldw_cnt_bad1 := by
  intro E W Y P _ _ _ _ _ _ cw e bad L2 L tg f g u hbad hL2
  refine (cnt_or_le _ _).trans (Nat.add_le_add hbad ?_)
  have h1 : cnt (fun μ : E =>
        ∃ Mg Mf : W, LdwNear2 cw e g f Mg Mf ∧ L Mf ≠ tg ∧ L Mg + μ * L Mf = u + μ * tg) ≤
      cnt (fun μ : E =>
        ∃ MM : W × W,
            LdwNear2 cw e g f MM.1 MM.2 ∧ (L MM.2 ≠ tg ∧ L MM.1 + μ * L MM.2 = u + μ * tg)) :=
    cnt_mono fun μ ⟨Mg, Mf, h⟩ => ⟨(Mg, Mf), h⟩
  refine h1.trans ((ldw_cnt_list (k := 1) fun MM _ => ?_).trans (by rw [Nat.mul_one]; exact hL2))
  refine cnt_le_one fun a b ha hb => ?_
  have h0 : L MM.2 - tg ≠ 0 := sub_ne_zero.mpr ha.1
  have h2 : (a - b) * (L MM.2 - tg) = 0 := by linear_combination ha.2 - hb.2
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right h0)

theorem ldw_cnt_bad2 : Spec.ldw_cnt_bad2 := by
  intro E W Y P _ _ _ _ cw e f g μ ms t
  by_cases h : LdwNear cw e (fun x => g x + μ • f x) ms
  · rw [cnt_false fun Q hQ => hQ.2 h]
    exact Nat.zero_le _
  · refine le_trans (cnt_mono fun Q hQ i => ?_)
      (Blocks.cnt_miss_le_of_lt (P := fun x => g x + μ • f x ≠ cw ms x) (not_le.mp h) t)
    exact fun hn => hn (hQ.1 i).symm

theorem ldw_back : Spec.ldw_back := by
  intro E W Y P _ _ _ _ _ _ cw e L tg f g u μ ms t Q hcw hL hb1 hb2 hacc
  have hnear : LdwNear cw e (fun x => g x + μ • f x) ms := by_contra fun hc => hb2 ⟨hacc.2, hc⟩
  have hS := hnear.card_agree
  have hline : LdwOn cw (fun x => g x + μ • f x) (ldwAgree cw (fun x => g x + μ • f x) ms) :=
    ⟨ms, fun x hx => mem_ldwAgree.1 hx⟩
  have hboth : LdwOn cw g (ldwAgree cw (fun x => g x + μ • f x) ms) ∧
      LdwOn cw f (ldwAgree cw (fun x => g x + μ • f x) ms) :=
    by_contra fun hc => hb1 (Or.inl ⟨_, hS, hline, hc⟩)
  refine ⟨hboth.2,
    fun M hM =>
      ⟨ldwNear_of_agree hS hM, by_contra fun hne => hb1 (Or.inr ⟨ms + (-μ) • M, M, ?_, hne, ?_⟩)⟩⟩
  · have h1 := cnt_add_card_le (P := fun x => g x ≠ cw (ms + (-μ) • M) x ∨ f x ≠ cw M x) (S := ldwAgree cw (fun x => g x + μ • f x) ms) fun x hx hn => by
      have hx1 : g x + μ • f x = cw ms x := mem_ldwAgree.1 hx
      have hx2 := hM x hx
      refine hn.elim (fun h => h ?_) fun h => h hx2
      rw [hcw, ← hx1, ← hx2, neg_smul, add_neg_cancel_right]
    unfold LdwNear2
    omega
  · rw [hL, hacc.1]
    ring

theorem ldw_unique : Spec.ldw_unique := by
  intro W Y P _ cw D f S M M' hD hS hM hM'
  by_contra hne
  have h1 := hD M M' hne
  have h2 := cnt_add_card_le (P := fun x => cw M x ≠ cw M' x) (S := S) fun x hx hn =>
    hn ((hM x hx).symm.trans (hM' x hx))
  omega

theorem ldw_complete : Spec.ldw_complete := by
  intro E W Y P _ _ _ _ _ cw L tg m h μ t Q hcw hL hm
  exact ⟨by rw [hL, hm], fun i => hcw h m μ (Q i)⟩

theorem ldw_law : Spec.ldw_law := by
  intro E W Y P _ _ _ _ _ _ cw L tg m μ hcw hL hm
  refine map_unif_reindex (Equiv.addRight (μ • m)) _ _ fun h => ?_
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · show L h = L (h + μ • m) - μ * tg
    rw [hL, hm]
    ring
  · funext x
    show cw h x = cw (h + μ • m) x - μ • cw m x
    rw [hcw, add_sub_cancel_right]

end Cb
