-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBaseThird.lean: proofs of `Spec.ldw_third` and `Spec.ldw_third_fold` of
Cb/Ld/LdBaseWords.lean: mutual correlated agreement on lines below a third of the distance, for the
image of any linear map cw : W → P → Y into words over a vector space Y.

Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. What they say: if two different words of the image differ at D positions or more and 3 e <
D, every line g + μ f (`Spec.ldw_third`; exceptional: on some set that misses at most e positions
the line is on the code while g and f are not both (`LdwExc` at the radius e,
Cb/Ld/LdBaseWords.lean)) and every line (1 - μ) g + μ f (`Spec.ldw_third_fold`) has at most e + 1
exceptional values μ.

Code/Third.lean proves the same bound, e + 1 exceptional values if 3 e < d, for interleaved words:
every row lies in one and the same subspace of scalar words (through it: `Spec.prox_third` of
Cb/Gen/CodeList.lean). Here a symbol is an element of a vector space and the code is any subspace of
words over it: interleaved rows are the case Y = rows → E with cw rowwise; a group of codes of
different lengths read at common positions is another case, and for it the bound here (e + 1, from
the distance of the group) is not the sum over the components.

The proof follows the steps of Code/Third.lean, and takes its three counting lemmas from there. A
set of positions is large if it misses at most e.
 1. Two different values at which the line is on the code on large sets determine N₀, N₁ in W with g
    = cw N₀ and f = cw N₁ on the intersection of the two sets.
 2. Wherever the line g + θ f is on the code on a large set S, it is cw N₀ + θ cw N₁ on S: the two
    words of the code agree on a set that misses at most 3 e < D positions.
 3. A position is wrong if (g, f) differs there from (cw N₀, cw N₁). At a wrong position the two
    lines meet for at most one θ.
 4. Counting pairs (value, wrong position of its set): with e + 2 values there are at most e wrong
    positions.
 5. An exceptional θ has a wrong position in its set; different values have different ones. So e + 2
    exceptional values would be at most e.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBaseWords
import Code.Third
import Mathlib.Tactic.Module

set_option autoImplicit false

namespace Cb
open Prob Finset

namespace LdwThird
variable {E W Y P : Type} [Field E] [AddCommGroup W] [Module E W] [AddCommGroup Y] [Module E Y]

/-- At the position x the line through g, f and the line through c₀, c₁ have the same value at θ. -/
def Meet (g f c₀ c₁ : P → Y) (θ : E) (x : P) : Prop := g x + θ • f x = c₀ x + θ • c₁ x

/-- The position x is wrong. -/
def Wrong (g f c₀ c₁ : P → Y) (x : P) : Prop := ¬ (g x = c₀ x ∧ f x = c₁ x)

/-- (Step 3.) -/
theorem meet_unique {g f c₀ c₁ : P → Y} {x : P} (hw : Wrong g f c₀ c₁ x) {θ θ' : E}
    (h : Meet g f c₀ c₁ θ x) (h' : Meet g f c₀ c₁ θ' x) : θ = θ' := by
  by_contra hne
  unfold Meet at h h'
  have h1 : (θ - θ') • (f x - c₁ x) = 0 := by
    have h2 : (g x + θ • f x) - (g x + θ' • f x) = (c₀ x + θ • c₁ x) - (c₀ x + θ' • c₁ x) := by
      rw [h, h']
    have h3 : (θ - θ') • (f x - c₁ x) =
        ((g x + θ • f x) - (g x + θ' • f x)) - ((c₀ x + θ • c₁ x) - (c₀ x + θ' • c₁ x)) := by module
    rw [h3, h2, sub_self]
  have hf : f x = c₁ x := sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hne))
  rw [hf] at h
  exact hw ⟨add_right_cancel h, hf⟩

/-- (Step 1.) -/
theorem line_of_two {cw : W → P → Y} (hcw : LdwLin (E := E) cw) (g f : P → Y) {x₁ x₂ : E}
    (hne : x₁ ≠ x₂) {S₁ S₂ : Finset P} {M₁ M₂ : W} (h₁ : ∀ x ∈ S₁, g x + x₁ • f x = cw M₁ x)
    (h₂ : ∀ x ∈ S₂, g x + x₂ • f x = cw M₂ x) :
    ∃ N₀ N₁ : W, ∀ x, x ∈ S₁ → x ∈ S₂ → g x = cw N₀ x ∧ f x = cw N₁ x := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hz : ∀ x, cw (0 : W) x = 0 := fun x => by
    have h := hcw 0 0 (1 : E) x
    rw [one_smul, one_smul, add_zero] at h
    exact (add_eq_left.mp h.symm)
  have hsm : ∀ (c : E) (b : W) x, cw (c • b) x = c • cw b x := fun c b x => by
    have h := hcw 0 b c x
    rwa [zero_add, hz, zero_add] at h
  refine ⟨M₁ + (-x₁) • ((x₂ - x₁)⁻¹ • (M₂ + (-1 : E) • M₁)),
    (x₂ - x₁)⁻¹ • (M₂ + (-1 : E) • M₁),
    fun x hx₁ hx₂ => ?_⟩
  have e₁ := h₁ x hx₁
  have e₂ := h₂ x hx₂
  have key : f x = cw ((x₂ - x₁)⁻¹ • (M₂ + (-1 : E) • M₁)) x := by
    rw [hsm, hcw, ← e₁, ← e₂]
    have : g x + x₂ • f x + (-1 : E) • (g x + x₁ • f x) = (x₂ - x₁) • f x := by module
    rw [this, smul_smul, inv_mul_cancel₀ hd, one_smul]
  refine ⟨?_, key⟩
  rw [hcw, ← key, ← e₁]
  module

variable [Fintype P]

/-- (Step 2.) -/
theorem meet_of_agree {cw : W → P → Y} (hcw : LdwLin (E := E) cw) {D k e : ℕ} (hD : LdwApart cw D)
    (hke : k + e < D) {g f : P → Y} {N₀ N₁ : W} {A : Finset P} (hA : Fintype.card P ≤ A.card + k)
    (hag : ∀ x ∈ A, g x = cw N₀ x ∧ f x = cw N₁ x) {θ : E} {S : Finset P}
    (hS : Fintype.card P ≤ S.card + e) (h : LdwOn cw (fun x => g x + θ • f x) S) :
    ∀ x ∈ S, Meet g f (cw N₀) (cw N₁) θ x := by
  classical
  obtain ⟨M, hM⟩ := h
  have hAS := Code.card_inter_large hA hS
  have hEq : cw M = cw (N₀ + θ • N₁) := by
    by_contra hne
    have h1 := hD _ _ hne
    have h2 := cnt_add_card_le (P := fun x => cw M x ≠ cw (N₀ + θ • N₁) x) (S := A ∩ S) fun x hx hn => hn (by
      rw [← hM x (mem_inter.mp hx).2, hcw]
      show g x + θ • f x = _
      rw [(hag x (mem_inter.mp hx).1).1, (hag x (mem_inter.mp hx).1).2])
    omega
  intro x hx
  have := hM x hx
  rw [hEq, hcw] at this
  exact this

/-- (Step 4.) -/
theorem card_wrong_le {g f c₀ c₁ : P → Y} {e : ℕ} {Wr : Finset P} (hW : ∀ x ∈ Wr, Wrong g f c₀ c₁ x)
    {Ys : Finset E} (hY : e + 2 ≤ Ys.card)
    (h : ∀ θ ∈ Ys, ∃ S : Finset P, Fintype.card P ≤ S.card + e ∧ ∀ x ∈ S, Meet g f c₀ c₁ θ x) :
    Wr.card ≤ e := by
  classical
  refine Code.bad_le_of_count
    hY (Code.card_mul_le_of_rows_cols Ys Wr (Meet g f c₀ c₁) (Wr.card - e) ?_ ?_)
  · intro θ hθ
    obtain ⟨S, hS, hm⟩ := h θ hθ
    refine ⟨Wr ∩ S, inter_subset_left, ?_, fun x hx => hm x (mem_inter.mp hx).2⟩
    have h1 : Wr ⊆ (Wr ∩ S) ∪ Sᶜ := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact mem_union_left _ (mem_inter.mpr ⟨hx, hxS⟩)
      · exact mem_union_right _ (mem_compl.mpr hxS)
    have h2 := (card_le_card h1).trans (card_union_le _ _)
    rw [card_compl] at h2
    omega
  · intro x hx a _ b _ ha hb
    exact meet_unique (hW x hx) ha hb

omit [Fintype P] in
/-- (Step 5.) -/
theorem card_le_card_wrong {g f c₀ c₁ : P → Y} {Wr : Finset P} (hW : ∀ x ∈ Wr, Wrong g f c₀ c₁ x)
    {Ys : Finset E} (h : ∀ θ ∈ Ys, ∃ x ∈ Wr, Meet g f c₀ c₁ θ x) : Ys.card ≤ Wr.card := by
  have h1 := Code.card_mul_le_of_rows_cols Ys Wr (Meet g f c₀ c₁) 1
    (fun θ hθ => by
      obtain ⟨x, hx, hm⟩ := h θ hθ
      exact ⟨{x}, singleton_subset_iff.mpr hx, by simp,
        fun i hi => by rw [mem_singleton.mp hi]; exact hm⟩)
    (fun x hx a _ b _ ha hb => meet_unique (hW x hx) ha hb)
  rwa [mul_one] at h1

end LdwThird

open LdwThird in
theorem ldw_third : Spec.ldw_third := by
  classical
  intro E W Y P _ _ _ _ _ _ _ cw D e g f hcw hD h3
  refine cnt_le_of_forall_finset fun Ys hYs => ?_
  by_contra hcard
  have hY : e + 2 ≤ Ys.card := by omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := one_lt_card.mp (by omega : 1 < Ys.card)
  obtain ⟨S₁, hS₁, ⟨M₁, h₁⟩, -⟩ := hYs x₁ hx₁
  obtain ⟨S₂, hS₂, ⟨M₂, h₂⟩, -⟩ := hYs x₂ hx₂
  obtain ⟨N₀, N₁, hag⟩ := line_of_two hcw g f hne h₁ h₂
  have hA : Fintype.card P ≤ (S₁ ∩ S₂).card + 2 * e := by
    have := Code.card_inter_large hS₁ hS₂
    omega
  have hmeet : ∀ (θ : E) (S : Finset P), Fintype.card P ≤ S.card + e →
      LdwOn cw (fun x => g x + θ • f x) S → ∀ x ∈ S, Meet g f (cw N₀) (cw N₁) θ x :=
    fun θ S hS hθ =>
      meet_of_agree hcw hD (by omega : 2 * e + e < D) hA
        (fun x hx => hag x (mem_inter.mp hx).1 (mem_inter.mp hx).2) hS hθ
  have hWr : ∀ x ∈ univ.filter (Wrong g f (cw N₀) (cw N₁)), Wrong g f (cw N₀) (cw N₁) x :=
    fun x hx => (mem_filter.mp hx).2
  have hle : (univ.filter (Wrong g f (cw N₀) (cw N₁))).card ≤
      e := card_wrong_le hWr hY fun θ hθ => by
    obtain ⟨S, hS, hon, -⟩ := hYs θ hθ
    exact ⟨S, hS, hmeet θ S hS hon⟩
  have hge : Ys.card ≤
      (univ.filter (Wrong g f (cw N₀) (cw N₁))).card := card_le_card_wrong hWr fun θ hθ => by
    obtain ⟨S, hS, hon, hnot⟩ := hYs θ hθ
    by_contra hno
    refine hnot ⟨⟨N₀, fun x hx => ?_⟩, ⟨N₁, fun x hx => ?_⟩⟩
    · by_contra hc
      exact hno ⟨x, mem_filter.mpr ⟨mem_univ x, fun h => hc h.1⟩, hmeet θ S hS hon x hx⟩
    · by_contra hc
      exact hno ⟨x, mem_filter.mpr ⟨mem_univ x, fun h => hc h.2⟩, hmeet θ S hS hon x hx⟩
  omega

theorem ldw_third_fold : Spec.ldw_third_fold := by
  intro E W Y P _ _ _ _ _ _ _ cw D e g f hcw hD h3
  refine le_trans (cnt_mono fun μ hμ => ?_)
    (ldw_third E W Y P cw D e g (fun x => f x - g x) hcw hD h3)
  obtain ⟨S, hS, ⟨M, hM⟩, hnot⟩ := hμ
  refine ⟨S, hS, ⟨M, fun x hx => ?_⟩, fun hb => hnot ⟨hb.1, ?_⟩⟩
  · rw [← hM x hx]
    module
  · obtain ⟨⟨Mg, hg⟩, ⟨Md, hd⟩⟩ := hb
    refine ⟨Mg + (1 : E) • Md, fun x hx => ?_⟩
    rw [hcw, ← hg x hx, ← hd x hx]
    module

end Cb
