-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Count.lean: discrete probability on Mathlib's PMF, and the adapter between counts and
probabilities.

The errors of the interactive oracle proof and of the code are stated as "at most k of the |C|
values of the challenge are bad", while the definition of the argument system in the random oracle
model (ZKCP/Defs.lean) is stated in probabilities. This file has the elementary probability that
both sides share and the conversion between them (the adapter), for C finite and non-empty:

    cnt P ≤ k   ↔   Pr[ P c | c ← C uniform ] ≤ k / |C|            (pr_unif_le_iff_cnt_le)

No oracle, field, code or protocol occurs here: everything is stated on Mathlib's types.

Contents
  1. counts: union bounds, products, bijections                     (cnt_*)
  2. averages E[F(a) | a ← p]                                        (expect_*)
  3. event probabilities Pr[a ∈ E | a ← p]: union bounds, Markov     (pr_*)
  4. pairs, dependent and independent                               (joint, prod)
  5. the adapter: uniform distributions are counts                  (*_unif*)

Shared with VCV-io (`expect_comm`): lean/CREDITS.md, section 4.
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring
import Prob.Basic
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal

namespace Prob

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Two more definitions (pr, expect and unif are in Prob/Basic.lean, cnt in Prob/Cnt.lean) -/

/-- The distribution of a pair of independent draws, a ← p and b ← q. -/
def prod (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

/-- The distribution of a pair (a, b) in which a ← p and then b ← g a, the second draw depending on
the first. -/
def joint (p : PMF α) (g : α → PMF β) : PMF (α × β) :=
  p.bind fun a => (g a).map fun b => (a, b)

/-! ## 1. Counts -/

section Counts
open Finset
variable {C D ι : Type}

/-- cnt is the cardinality of the filtered set, for every enumeration and every decision
procedure. -/
theorem cnt_eq_card_filter [Fintype C] (P : C → Prop) [DecidablePred P] :
    cnt P = (univ.filter P).card := by
  unfold cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem cnt_congr [Finite C] {P Q : C → Prop} (h : ∀ c, P c ↔ Q c) : cnt P = cnt Q := by
  have : P = Q := funext fun c => propext (h c)
  rw [this]

theorem cnt_le_card [Fintype C] (P : C → Prop) : cnt P ≤ Fintype.card C := by
  classical
  rw [cnt_eq_card_filter]
  exact card_le_univ _

theorem cnt_true [Fintype C] : cnt (fun _ : C => True) = Fintype.card C := by
  classical
  rw [cnt_eq_card_filter]
  simp

/-- To bound a count by k it suffices to bound by k every finite set of elements with the
property. -/
theorem cnt_le_of_forall_finset [Finite C] {P : C → Prop} {k : ℕ}
    (h : ∀ Y : Finset C, (∀ x ∈ Y, P x) → Y.card ≤ k) : cnt P ≤ k := by
  classical
  cases nonempty_fintype C
  rw [cnt_eq_card_filter]
  exact h _ (fun x hx => (mem_filter.mp hx).2)

/-- A finite set of elements with the property has at most as many elements as the count. -/
theorem card_le_cnt [Finite C] {P : C → Prop} (Y : Finset C) (h : ∀ x ∈ Y, P x) :
    Y.card ≤ cnt P := by
  classical
  cases nonempty_fintype C
  rw [cnt_eq_card_filter]
  exact card_le_card fun x hx => mem_filter.mpr ⟨mem_univ x, h x hx⟩

/-- A property that fails on the set S holds of at most |C| - |S| elements. -/
theorem cnt_add_card_le [Fintype C] {P : C → Prop} {S : Finset C} (h : ∀ j ∈ S, ¬ P j) :
    cnt P + S.card ≤ Fintype.card C := by
  classical
  rw [cnt_eq_card_filter]
  have hdis : Disjoint (univ.filter P) S :=
    Finset.disjoint_left.mpr fun j hj hS => h j hS (mem_filter.mp hj).2
  rw [← card_union_of_disjoint hdis]
  exact card_le_univ _

/-- A property and its negation partition the type. -/
theorem cnt_add_cnt_not [Fintype C] (P : C → Prop) :
    cnt P + cnt (fun c => ¬ P c) = Fintype.card C := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter]
  exact card_filter_add_card_filter_not (s := univ) P

/-- Union bound for two bad sets of one challenge. -/
theorem cnt_or_le [Fintype C] (P Q : C → Prop) : cnt (fun c => P c ∨ Q c) ≤ cnt P + cnt Q := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter, cnt_eq_card_filter, filter_or]
  exact card_union_le _ _

/-- Union bound in the form in which it is used: whatever is bad is bad for one of two reasons. -/
theorem cnt_le_add [Fintype C] {P Q R : C → Prop} (h : ∀ c, P c → Q c ∨ R c) :
    cnt P ≤ cnt Q + cnt R :=
  (cnt_mono h).trans (cnt_or_le Q R)

/-- Union bound over a finite family of bad sets of one challenge. -/
theorem cnt_exists_le [Fintype C] [Fintype ι] (P : ι → C → Prop) :
    cnt (fun c => ∃ i, P i c) ≤ ∑ i, cnt (P i) := by
  classical
  simp only [cnt_eq_card_filter]
  have : (univ.filter fun c => ∃ i, P i c) = univ.biUnion fun i => univ.filter (P i) := by
    ext c; simp
  rw [this]
  exact card_biUnion_le

/-- Union bound over a finite set of indices. -/
theorem cnt_exists_mem_le [Fintype C] (s : Finset ι) (P : ι → C → Prop) :
    cnt (fun c => ∃ i ∈ s, P i c) ≤ ∑ i ∈ s, cnt (P i) := by
  classical
  simp only [cnt_eq_card_filter]
  have : (univ.filter fun c => ∃ i ∈ s, P i c) = s.biUnion fun i => univ.filter (P i) := by
    ext c; simp
  rw [this]
  exact card_biUnion_le

/-- Union bound with the same bound k for each member of the family. -/
theorem cnt_exists_le_mul [Fintype C] [Fintype ι] (P : ι → C → Prop)
    (k : ℕ) (h : ∀ i, cnt (P i) ≤ k) :
    cnt (fun c => ∃ i, P i c) ≤ Fintype.card ι * k :=
  (cnt_exists_le P).trans ((sum_le_sum fun i _ => h i).trans (by simp))

/-- A property that holds of at most one value has count at most 1. -/
theorem cnt_le_one [Fintype C] {P : C → Prop} (h : ∀ a b, P a → P b → a = b) : cnt P ≤ 1 := by
  classical
  rw [cnt_eq_card_filter, card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  exact h a b ha hb

theorem cnt_eq_const [Fintype C] (v : C) : cnt (fun c => c = v) = 1 := by
  classical
  rw [cnt_eq_card_filter, filter_eq' univ v]
  simp

/-- cnt is invariant under a bijection of the challenge space. -/
theorem cnt_equiv [Fintype C] [Fintype D] (e : C ≃ D) (P : D → Prop) :
    cnt (fun c => P (e c)) = cnt P := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter]
  exact card_equiv e (by simp)

/-- For a pair of challenges, the count is the sum, over the first, of the counts over the
second. -/
theorem cnt_prod_eq_sum [Fintype C] [Fintype D] (P : C × D → Prop) :
    cnt P = ∑ c, cnt fun d => P (c, d) := by
  classical
  simp only [cnt_eq_card_filter, card_filter]
  rw [← univ_product_univ, sum_product]

/-- The fibres of a function partition its domain. -/
theorem sum_cnt_fiber [Fintype C] [Fintype D] (f : C → D) :
    ∑ d, cnt (fun c => f c = d) = Fintype.card C := by
  classical
  simp only [cnt_eq_card_filter]
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise fun x _ => mem_univ (f x)).symm

/-- If for every first challenge at most k second challenges are bad, at most |C| k pairs are
bad. -/
theorem cnt_prod_le [Fintype C] [Fintype D] (P : C × D → Prop) (k : ℕ)
    (h : ∀ c, cnt (fun d => P (c, d)) ≤ k) : cnt P ≤ Fintype.card C * k := by
  rw [cnt_prod_eq_sum]
  exact (sum_le_sum fun c _ => h c).trans (by simp)

/-- Independent conditions on the two components multiply. -/
theorem cnt_and_prod [Fintype C] [Fintype D] (P : C → Prop) (Q : D → Prop) :
    cnt (fun x : C × D => P x.1 ∧ Q x.2) = cnt P * cnt Q := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter, cnt_eq_card_filter]
  have : (univ.filter fun x : C × D => P x.1 ∧ Q x.2) = (univ.filter P) ×ˢ (univ.filter Q) := by
    ext x; simp
  rw [this, card_product]

theorem cnt_fst [Fintype C] [Fintype D] (P : C → Prop) :
    cnt (fun x : C × D => P x.1) = cnt P * Fintype.card D := by
  rw [← cnt_true (C := D), ← cnt_and_prod]
  exact cnt_congr fun x => by simp

theorem cnt_snd [Fintype C] [Fintype D] (Q : D → Prop) :
    cnt (fun x : C × D => Q x.2) = Fintype.card C * cnt Q := by
  rw [← cnt_true (C := C), ← cnt_and_prod]
  exact cnt_congr fun x => by simp

/-- Two rounds: a pair is bad if the first challenge is bad (at most k₁ values) or, the first being
good, the second is bad (at most k₂ values).  This is the count behind k₁/|C| + k₂/|D|. -/
theorem cnt_two_rounds_le [Fintype C] [Fintype D] (P : C × D → Prop) (B : C → Prop) (k₁ k₂ : ℕ)
    (h₁ : cnt B ≤ k₁) (h₂ : ∀ c, ¬ B c → cnt (fun d => P (c, d)) ≤ k₂) :
    cnt P ≤ k₁ * Fintype.card D + Fintype.card C * k₂ := by
  have hsplit : cnt P ≤ cnt (fun x : C × D => B x.1) + cnt (fun x : C × D => ¬ B x.1 ∧ P x) :=
    cnt_le_add fun x hx => by
      by_cases hb : B x.1
      · exact Or.inl hb
      · exact Or.inr ⟨hb, hx⟩
  refine hsplit.trans (Nat.add_le_add ?_ ?_)
  · rw [cnt_fst]
    exact Nat.mul_le_mul_right _ h₁
  · refine cnt_prod_le _ k₂ fun c => ?_
    by_cases hb : B c
    · rw [cnt_false fun d hd => hd.1 hb]
      exact Nat.zero_le _
    · exact (cnt_mono fun d hd => hd.2).trans (h₂ c hb)

/-- The lists of q entries that all have the property P number (cnt P)^q: the entries are
independent. -/
theorem cnt_forall_pow [Fintype C] (P : C → Prop) (q : ℕ) :
    cnt (fun I : Fin q → C => ∀ j, P (I j)) = cnt P ^ q := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter]
  have hset : (univ.filter fun I : Fin q → C => ∀ j, P (I j))
      = Fintype.piFinset (fun _ : Fin q => univ.filter P) := by
    ext I
    simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin]

/-- Independent conditions on all coordinates of a tuple of challenges multiply. -/
theorem cnt_forall_pi [Fintype ι] [DecidableEq ι] {A : ι → Type}
    [∀ i, Fintype (A i)] (P : ∀ i, A i → Prop) :
    cnt (fun f : ∀ i, A i => ∀ i, P i (f i)) = ∏ i, cnt (P i) := by
  classical
  simp only [cnt_eq_card_filter]
  have hset : (univ.filter fun f : ∀ i, A i => ∀ i, P i (f i))
      = Fintype.piFinset (fun i => univ.filter (P i)) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset]

/-- A property of one coordinate has the same probability on a tuple of challenges as on that
coordinate. -/
theorem cnt_pi_coord [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
    (i₀ : ι) (P : A i₀ → Prop) :
    cnt (fun f : ∀ i, A i => P (f i₀)) * Fintype.card (A i₀) = cnt P * Fintype.card (∀ i, A i) := by
  classical
  let e := Equiv.piSplitAt i₀ A
  have h1 : cnt (fun f : ∀ i, A i => P (f i₀)) =
      cnt (fun x : A i₀ × (∀ j : {j // j ≠ i₀}, A j) => P x.1) :=
    cnt_equiv e (fun x : A i₀ × (∀ j : {j // j ≠ i₀}, A j) => P x.1)
  have h3 : Fintype.card (∀ i, A i) =
      Fintype.card (A i₀) * Fintype.card (∀ j : {j // j ≠ i₀}, A j) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [h1, cnt_fst, h3]
  ring

end Counts

/-! ## 2. Averages -/

section Expect

theorem expect_pure (a : α) (F : α → ℝ≥0∞) : expect (PMF.pure a) F = F a := by
  classical
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

/-- The law of total expectation. -/
theorem expect_bind (p : PMF α) (g : α → PMF β) (F : β → ℝ≥0∞) :
    expect (p.bind g) F = expect p fun a => expect (g a) F := by
  unfold expect
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc]

theorem expect_map (p : PMF α) (h : α → β) (F : β → ℝ≥0∞) :
    expect (p.map h) F = expect p fun a => F (h a) := by
  change expect (p.bind (PMF.pure ∘ h)) F = _
  rw [expect_bind]; simp [expect_pure]

theorem expect_mono (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a, F a ≤ G a) : expect p F ≤ expect p G :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

/-- Only the values that p can take matter for a comparison of averages. -/
theorem expect_mono_support (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a ∈ p.support, F a ≤ G a) :
    expect p F ≤ expect p G :=
  ENNReal.tsum_le_tsum fun a => by
    by_cases ha : p a = 0
    · simp [ha]
    · gcongr; exact h a ((p.mem_support_iff a).2 ha)

theorem expect_congr (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a, F a = G a) :
    expect p F = expect p G := by
  have : F = G := funext h
  rw [this]

theorem expect_congr_support (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a ∈ p.support, F a = G a) :
    expect p F = expect p G :=
  le_antisymm (expect_mono_support p fun a ha => (h a ha).le)
    (expect_mono_support p fun a ha => (h a ha).ge)

theorem expect_add (p : PMF α) (F G : α → ℝ≥0∞) :
    expect p (fun a => F a + G a) = expect p F + expect p G := by
  unfold expect; simp only [mul_add]; exact ENNReal.tsum_add

theorem expect_const (p : PMF α) (c : ℝ≥0∞) : expect p (fun _ => c) = c := by
  unfold expect; rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem expect_zero (p : PMF α) : expect p (fun _ => 0) = 0 := expect_const p 0

theorem expect_const_mul (p : PMF α) (c : ℝ≥0∞) (F : α → ℝ≥0∞) :
    expect p (fun a => c * F a) = c * expect p F := by
  unfold expect
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => mul_left_comm _ _ _

theorem expect_mul_const (p : PMF α) (F : α → ℝ≥0∞) (c : ℝ≥0∞) :
    expect p (fun a => F a * c) = expect p F * c := by
  unfold expect
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun a => (mul_assoc _ _ _).symm

theorem expect_finset_sum {ι : Type w} (p : PMF α) (s : Finset ι) (F : ι → α → ℝ≥0∞) :
    expect p (fun a => ∑ i ∈ s, F i a) = ∑ i ∈ s, expect p (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expect_zero]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [expect_add, ih]

theorem expect_tsum {ι : Type w} (p : PMF α) (F : ι → α → ℝ≥0∞) :
    expect p (fun a => ∑' i, F i a) = ∑' i, expect p (F i) := by
  unfold expect
  simp only [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

theorem expect_fintype [Fintype α] (p : PMF α) (F : α → ℝ≥0∞) : expect p F = ∑ a, p a * F a :=
  tsum_fintype _

/-- An average is at most any bound that holds for all values that p can take. -/
theorem expect_le_of_forall_le
    (p : PMF α) {F : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a ∈ p.support, F a ≤ c) : expect p F ≤ c :=
  (expect_mono_support p h).trans (expect_const p c).le

/-- Averages over two independent draws may be taken in either order. -/
theorem expect_comm (p : PMF α) (q : PMF β) (F : α → β → ℝ≥0∞) :
    (expect p fun a => expect q fun b => F a b) = expect q fun b => expect p fun a => F a b := by
  unfold expect
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => mul_left_comm _ _ _

open Classical in
/-- The probability of one point is the average of its indicator. -/
theorem apply_eq_expect (p : PMF α) (a : α) : p a = expect p fun b => if b = a then 1 else 0 := by
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [hb]

open Classical in
theorem expect_ite_eq (p : PMF α) (a : α) (x : ℝ≥0∞) :
    (expect p fun b => if b = a then x else 0) = p a * x := by
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [hb]

/-- Two distributions with the same averages are equal. -/
theorem ext_of_expect {p q : PMF α} (h : ∀ F, expect p F = expect q F) : p = q := by
  classical
  exact PMF.ext fun a => by rw [apply_eq_expect p a, apply_eq_expect q a, h]

end Expect

/-! ## 3. Event probabilities -/

section Pr

theorem pr_eq_tsum_indicator (p : PMF α) (E : Set α) : pr p E = ∑' a, E.indicator p a :=
  PMF.toOuterMeasure_apply p E

open Classical in
theorem pr_eq_expect (p : PMF α) (E : Set α) :
    pr p E = expect p fun a => if a ∈ E then 1 else 0 := by
  unfold pr expect
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun a => ?_
  by_cases h : a ∈ E <;> simp [h]

open Classical in
theorem pr_pure (a : α) (E : Set α) : pr (PMF.pure a) E = if a ∈ E then 1 else 0 := by
  rw [pr_eq_expect, expect_pure]

/-- The law of total probability. -/
theorem pr_bind (p : PMF α) (g : α → PMF β) (E : Set β) :
    pr (p.bind g) E = expect p fun a => pr (g a) E :=
  PMF.toOuterMeasure_bind_apply p g E

theorem pr_map (p : PMF α) (f : α → β) (E : Set β) : pr (p.map f) E = pr p (f ⁻¹' E) :=
  PMF.toOuterMeasure_map_apply f p E

theorem pr_singleton (p : PMF α) (a : α) : pr p {a} = p a :=
  PMF.toOuterMeasure_apply_singleton p a

theorem pr_mono (p : PMF α) {E F : Set α} (h : E ⊆ F) : pr p E ≤ pr p F :=
  p.toOuterMeasure.mono h

/-- Only the values that p can take matter for a comparison of events. -/
theorem pr_mono_support (p : PMF α) {E F : Set α} (h : ∀ a ∈ p.support, a ∈ E → a ∈ F) :
    pr p E ≤ pr p F := by
  classical
  rw [pr_eq_expect, pr_eq_expect]
  refine expect_mono_support p fun a ha => ?_
  by_cases hE : a ∈ E
  · simp [hE, h a ha hE]
  · simp [hE]

theorem pr_congr_support (p : PMF α) {E F : Set α} (h : ∀ a ∈ p.support, (a ∈ E ↔ a ∈ F)) :
    pr p E = pr p F :=
  le_antisymm (pr_mono_support p fun a ha => (h a ha).1) (pr_mono_support p fun a ha => (h a ha).2)

theorem pr_le_one (p : PMF α) (E : Set α) : pr p E ≤ 1 := by
  classical
  rw [pr_eq_expect]
  calc _ ≤ expect p (fun _ => 1) := expect_mono p fun a => by split_ifs <;> simp
    _ = 1 := expect_const p 1

theorem pr_ne_top (p : PMF α) (E : Set α) : pr p E ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (pr_le_one p E)

@[simp] theorem pr_empty (p : PMF α) : pr p ∅ = 0 := by
  classical
  rw [pr_eq_expect]; simp [expect_zero]

@[simp] theorem pr_univ (p : PMF α) : pr p Set.univ = 1 := by
  classical
  rw [pr_eq_expect]; simp [expect_const]

theorem pr_add_compl (p : PMF α) (E : Set α) : pr p E + pr p Eᶜ = 1 := by
  classical
  rw [pr_eq_expect, pr_eq_expect, ← expect_add]
  calc _ = expect p (fun _ => 1) := expect_congr p fun a => by by_cases h : a ∈ E <;> simp [h]
    _ = 1 := expect_const p 1

theorem pr_compl (p : PMF α) (E : Set α) : pr p Eᶜ = 1 - pr p E := by
  rw [← pr_add_compl p E, ENNReal.add_sub_cancel_left (pr_ne_top p E)]

/-- An event splits along any other event. -/
theorem pr_inter_add_diff (p : PMF α) (E F : Set α) : pr p (E ∩ F) + pr p (E \ F) = pr p E := by
  classical
  rw [pr_eq_expect, pr_eq_expect, pr_eq_expect, ← expect_add]
  refine expect_congr p fun a => ?_
  by_cases hE : a ∈ E <;> by_cases hF : a ∈ F <;> simp [hE, hF]

/-- Union bound for two events. -/
theorem pr_union_le (p : PMF α) (E F : Set α) : pr p (E ∪ F) ≤ pr p E + pr p F := by
  classical
  rw [pr_eq_expect, pr_eq_expect, pr_eq_expect, ← expect_add]
  refine expect_mono p fun a => ?_
  by_cases hE : a ∈ E <;> by_cases hF : a ∈ F <;> simp [hE, hF]

theorem pr_union_of_disjoint (p : PMF α) {E F : Set α} (h : Disjoint E F) :
    pr p (E ∪ F) = pr p E + pr p F := by
  classical
  rw [pr_eq_expect, pr_eq_expect, pr_eq_expect, ← expect_add]
  refine expect_congr p fun a => ?_
  by_cases hE : a ∈ E
  · have hF : a ∉ F := fun hF => Set.disjoint_left.1 h hE hF
    simp [hE, hF]
  · by_cases hF : a ∈ F <;> simp [hE, hF]

/-- Union bound in the form in which it is used: whatever is in E is in F or in G. -/
theorem pr_le_add (p : PMF α) {E F G : Set α} (h : E ⊆ F ∪ G) : pr p E ≤ pr p F + pr p G :=
  (pr_mono p h).trans (pr_union_le p F G)

/-- Union bound over any family of events (the sum may be infinite). -/
theorem pr_iUnion_le {ι : Type w} (p : PMF α) (E : ι → Set α) :
    pr p (⋃ i, E i) ≤ ∑' i, pr p (E i) := by
  classical
  simp only [pr_eq_expect]
  rw [← expect_tsum]
  refine expect_mono p fun a => ?_
  by_cases h : a ∈ ⋃ i, E i
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h
    calc (if a ∈ ⋃ i, E i then (1 : ℝ≥0∞) else 0) = if a ∈ E i then 1 else 0 := by simp [h, hi]
      _ ≤ ∑' j, if a ∈ E j then 1 else 0 := ENNReal.le_tsum i
  · simp [h]

/-- Union bound over a finite set of indices. -/
theorem pr_biUnion_finset_le {ι : Type w} (p : PMF α) (s : Finset ι) (E : ι → Set α) :
    pr p (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, pr p (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    exact (pr_union_le p _ _).trans (by gcongr)

/-- Union bound over a finite family, for properties. -/
theorem pr_exists_le {ι : Type w} [Fintype ι] (p : PMF α) (P : ι → α → Prop) :
    pr p {a | ∃ i, P i a} ≤ ∑ i, pr p {a | P i a} := by
  have h : {a | ∃ i, P i a} = ⋃ i ∈ (Finset.univ : Finset ι), {a | P i a} := by
    ext a; simp
  rw [h]
  exact pr_biUnion_finset_le p Finset.univ _

/-- Union bound with the same bound for each member of a finite family. -/
theorem pr_exists_le_mul {ι : Type w} [Fintype ι] (p : PMF α) (P : ι → α → Prop) (ε : ℝ≥0∞)
    (h : ∀ i, pr p {a | P i a} ≤ ε) : pr p {a | ∃ i, P i a} ≤ Fintype.card ι * ε :=
  (pr_exists_le p P).trans ((Finset.sum_le_sum fun i _ => h i).trans (by simp))

/-- Markov's inequality. -/
theorem mul_pr_le_expect (p : PMF α) (F : α → ℝ≥0∞) (c : ℝ≥0∞) :
    c * pr p {a | c ≤ F a} ≤ expect p F := by
  classical
  rw [pr_eq_expect, ← expect_const_mul]
  refine expect_mono p fun a => ?_
  by_cases h : c ≤ F a
  · simp [h]
  · simp [h]

/-- The average of a quantity with values in [0,1] that is at most ε outside the event B is at most
Pr[B] + ε. -/
theorem expect_le_pr_add (p : PMF α) (F : α → ℝ≥0∞) (B : Set α) {ε : ℝ≥0∞} (h₁ : ∀ a, F a ≤ 1)
    (h : ∀ a ∈ p.support, a ∉ B → F a ≤ ε) : expect p F ≤ pr p B + ε := by
  classical
  rw [pr_eq_expect p B]
  calc expect p F ≤ expect p (fun a => (if a ∈ B then 1 else 0) + ε) := by
        refine expect_mono_support p fun a ha => ?_
        by_cases hB : a ∈ B
        · simp only [hB, if_true]
          exact (h₁ a).trans le_self_add
        · simpa [hB] using h a ha hB
    _ = expect p (fun a => if a ∈ B then 1 else 0) + ε := by rw [expect_add, expect_const]

/-- A bound that holds after every first step holds for the two steps together. -/
theorem pr_bind_le_of_forall (p : PMF α) (g : α → PMF β) (E : Set β) {ε : ℝ≥0∞}
    (h : ∀ a ∈ p.support, pr (g a) E ≤ ε) : pr (p.bind g) E ≤ ε := by
  rw [pr_bind]
  exact expect_le_of_forall_le p h

/-- Two steps: the first step is bad with probability Pr[B]; after a good first step the event has
probability at most ε. Then the event has probability at most Pr[B] + ε. -/
theorem pr_bind_le_add (p : PMF α) (g : α → PMF β) (E : Set β) (B : Set α) {ε : ℝ≥0∞}
    (h : ∀ a ∈ p.support, a ∉ B → pr (g a) E ≤ ε) : pr (p.bind g) E ≤ pr p B + ε := by
  rw [pr_bind]
  exact expect_le_pr_add p _ B (fun a => pr_le_one (g a) E) h

/-- Two distributions with the same event probabilities are equal. -/
theorem ext_of_pr {p q : PMF α} (h : ∀ E, pr p E = pr q E) : p = q :=
  PMF.ext fun a => by rw [← pr_singleton p a, ← pr_singleton q a, h]

/-- An event that contains every value that p can take has probability 1. -/
theorem pr_eq_one_of_support_subset (p : PMF α) {E : Set α} (h : p.support ⊆ E) : pr p E = 1 := by
  rw [← pr_univ p]
  exact pr_congr_support p fun a ha => ⟨fun _ => trivial, fun _ => h ha⟩

/-- An event that contains no value that p can take has probability 0. -/
theorem pr_eq_zero_of_forall_not_mem (p : PMF α) {E : Set α} (h : ∀ a ∈ p.support, a ∉ E) :
    pr p E = 0 := by
  rw [← pr_empty p]
  exact pr_congr_support p fun a ha => ⟨fun hE => (h a ha hE).elim, fun hE => hE.elim⟩

end Pr

/-! ## 4. Pairs: dependent and independent -/

section Prod

theorem expect_joint (p : PMF α) (g : α → PMF β) (F : α × β → ℝ≥0∞) :
    expect (joint p g) F = expect p fun a => expect (g a) fun b => F (a, b) := by
  unfold joint
  rw [expect_bind]
  exact expect_congr p fun a => expect_map (g a) _ F

theorem joint_apply (p : PMF α) (g : α → PMF β) (a : α) (b : β) :
    joint p g (a, b) = p a * g a b := by
  classical
  rw [apply_eq_expect (joint p g), expect_joint, ← expect_ite_eq p a (g a b)]
  refine expect_congr p fun a' => ?_
  by_cases ha : a' = a
  · subst ha
    simp only [Prod.mk.injEq, true_and, if_true]
    exact (apply_eq_expect (g a') b).symm
  · simp [ha, expect_zero]

/-- The probability of an event about a pair, computed one draw after the other. -/
theorem pr_joint (p : PMF α) (g : α → PMF β) (S : Set (α × β)) :
    pr (joint p g) S = expect p fun a => pr (g a) {b | (a, b) ∈ S} := by
  unfold joint
  rw [pr_bind]
  exact expect_congr p fun a => pr_map (g a) _ S

theorem map_fst_joint (p : PMF α) (g : α → PMF β) : (joint p g).map Prod.fst = p :=
  ext_of_expect fun F => by
    rw [expect_map, expect_joint]
    exact expect_congr p fun a => expect_const (g a) (F a)

theorem map_snd_joint (p : PMF α) (g : α → PMF β) : (joint p g).map Prod.snd = p.bind g :=
  ext_of_expect fun F => by
    rw [expect_map, expect_joint, expect_bind]

theorem joint_const (p : PMF α) (q : PMF β) : joint p (fun _ => q) = prod p q := rfl

theorem expect_prod (p : PMF α) (q : PMF β) (F : α × β → ℝ≥0∞) :
    expect (prod p q) F = expect p fun a => expect q fun b => F (a, b) := by
  unfold prod
  rw [expect_bind]
  exact expect_congr p fun a => expect_map q _ F

theorem prod_apply (p : PMF α) (q : PMF β) (a : α) (b : β) : prod p q (a, b) = p a * q b := by
  classical
  rw [apply_eq_expect (prod p q), expect_prod, apply_eq_expect p a,
    apply_eq_expect q b, ← expect_mul_const]
  refine expect_congr p fun a' => ?_
  rw [← expect_const_mul]
  refine expect_congr q fun b' => ?_
  by_cases ha : a' = a <;> by_cases hb : b' = b <;> simp [ha, hb]

theorem pr_prod (p : PMF α) (q : PMF β) (S : Set (α × β)) :
    pr (prod p q) S = expect p fun a => pr q {b | (a, b) ∈ S} :=
  pr_joint p (fun _ => q) S

/-- Independent events multiply. -/
theorem pr_prod_rect (p : PMF α) (q : PMF β) (A : Set α) (B : Set β) :
    pr (prod p q) (A ×ˢ B) = pr p A * pr q B := by
  classical
  rw [pr_eq_expect, expect_prod, pr_eq_expect p A, pr_eq_expect q B, ← expect_mul_const]
  refine expect_congr p fun a => ?_
  rw [← expect_const_mul]
  refine expect_congr q fun b => ?_
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ B <;> simp [ha, hb]

theorem map_fst_prod (p : PMF α) (q : PMF β) : (prod p q).map Prod.fst = p :=
  ext_of_expect fun F => by
    rw [expect_map, expect_prod]
    exact expect_congr p fun a => expect_const q (F a)

theorem map_snd_prod (p : PMF α) (q : PMF β) : (prod p q).map Prod.snd = q :=
  ext_of_expect fun F => by
    rw [expect_map, expect_prod]
    exact expect_const p (expect q F)

/-- A pair of independent draws may be made in either order. -/
theorem map_swap_prod (p : PMF α) (q : PMF β) : (prod p q).map Prod.swap = prod q p :=
  ext_of_expect fun F => by
    rw [expect_map, expect_prod, expect_prod, expect_comm]
    rfl

/-- Sampling a, then b independently of a, and then continuing is the same as continuing from an
independent pair. -/
theorem bind_bind_eq_prod_bind (p : PMF α) (q : PMF β) (g : α → β → PMF γ) :
    (p.bind fun a => q.bind fun b => g a b) = (prod p q).bind fun x => g x.1 x.2 :=
  ext_of_expect fun F => by
    simp only [expect_bind, expect_prod]

/-- Two independent draws may be exchanged inside a longer experiment. -/
theorem bind_comm (p : PMF α) (q : PMF β) (g : α → β → PMF γ) :
    (p.bind fun a => q.bind fun b => g a b) = q.bind fun b => p.bind fun a => g a b :=
  ext_of_expect fun F => by
    simp only [expect_bind]
    exact expect_comm p q _

end Prod

/-! ## 5. The adapter: uniform distributions are counts -/

section Unif
variable {C D : Type}

theorem card_ne_zero' (C : Type u) [Fintype C] [Nonempty C] : (Fintype.card C : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

theorem card_ne_top' (C : Type u) [Fintype C] : (Fintype.card C : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.natCast_ne_top _

/-- The average over a uniform draw is the sum divided by the number of values. -/
theorem expect_unif {C : Type u} [Fintype C] [Nonempty C] (F : C → ℝ≥0∞) :
    expect (unif C) F = (∑ c, F c) / Fintype.card C := by
  unfold expect
  rw [tsum_fintype, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by rw [PMF.uniformOfFintype_apply, mul_comm]

/-- `expect_unif`, written with the weight 1/|C| at each term. -/
theorem expect_unif_sum {C : Type u} [Fintype C] [Nonempty C] (F : C → ℝ≥0∞) :
    expect (unif C) F = ∑ c, (Fintype.card C : ℝ≥0∞)⁻¹ * F c := by
  unfold expect; rw [tsum_fintype]; simp [PMF.uniformOfFintype_apply]

/-- The adapter, as an equation: Pr[ P c | c uniform in C ] = (number of c with P c) / |C|. -/
theorem pr_unif_eq [Fintype C] [Nonempty C] (P : C → Prop) :
    pr (unif C) {c | P c} = (cnt P : ℝ≥0∞) / Fintype.card C := by
  classical
  rw [pr_eq_expect, expect_unif, cnt_eq_card_filter]
  congr 1
  simp only [Set.mem_setOf_eq]
  exact Finset.sum_boole _ _

/-- The adapter against an arbitrary bound ε. -/
theorem pr_unif_le_iff [Fintype C] [Nonempty C] (P : C → Prop) (ε : ℝ≥0∞) :
    pr (unif C) {c | P c} ≤ ε ↔ (cnt P : ℝ≥0∞) ≤ ε * Fintype.card C := by
  rw [pr_unif_eq, ENNReal.div_le_iff (card_ne_zero' C) (card_ne_top' C)]

/-- The adapter: at most k values of the challenge are bad if and only if a challenge drawn
uniformly is bad with probability at most k / |C|. -/
theorem pr_unif_le_iff_cnt_le [Fintype C] [Nonempty C] (P : C → Prop) (k : ℕ) :
    pr (unif C) {c | P c} ≤ (k : ℝ≥0∞) / Fintype.card C ↔ cnt P ≤ k := by
  rw [pr_unif_le_iff, ENNReal.div_mul_cancel (card_ne_zero' C) (card_ne_top' C), Nat.cast_le]

theorem pr_unif_le_of_cnt_le [Fintype C] [Nonempty C] {P : C → Prop} {k : ℕ} (h : cnt P ≤ k) :
    pr (unif C) {c | P c} ≤ (k : ℝ≥0∞) / Fintype.card C :=
  (pr_unif_le_iff_cnt_le P k).2 h

theorem cnt_le_of_pr_unif_le [Fintype C] [Nonempty C] {P : C → Prop} {k : ℕ}
    (h : pr (unif C) {c | P c} ≤ (k : ℝ≥0∞) / Fintype.card C) : cnt P ≤ k :=
  (pr_unif_le_iff_cnt_le P k).1 h

/-- The adapter for bounds "at most m / D" on a challenge space whose size is not D (for instance a
tuple of field elements, with D the size of the field): cnt P * D ≤ m * |C|. -/
theorem pr_unif_le_div_iff [Fintype C] [Nonempty C] (P : C → Prop) (m D : ℕ) (hD : D ≠ 0) :
    pr (unif C) {c | P c} ≤ (m : ℝ≥0∞) / D ↔ cnt P * D ≤ m * Fintype.card C := by
  have hD0 : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD
  have hDt : (D : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top D
  rw [pr_unif_le_iff, ← ENNReal.mul_div_right_comm,
    ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDt)]
  exact_mod_cast Iff.rfl

/-- The adapter in real numbers. -/
theorem toReal_pr_unif [Fintype C] [Nonempty C] (P : C → Prop) :
    (pr (unif C) {c | P c}).toReal = (cnt P : ℝ) / Fintype.card C := by
  rw [pr_unif_eq, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- The adapter against a bound given as a real number. -/
theorem pr_unif_le_ofReal_iff [Fintype C] [Nonempty C] (P : C → Prop) {x : ℝ} (hx : 0 ≤ x) :
    pr (unif C) {c | P c} ≤ ENNReal.ofReal x ↔ (cnt P : ℝ) / Fintype.card C ≤ x := by
  rw [← toReal_pr_unif, ENNReal.le_ofReal_iff_toReal_le (pr_ne_top _ _) hx]

/-- Total probability over a uniform first step. -/
theorem pr_unif_bind {C : Type u} [Fintype C] [Nonempty C] (g : C → PMF β) (E : Set β) :
    pr ((unif C).bind g) E = (∑ c, pr (g c) E) / Fintype.card C := by
  rw [pr_bind, expect_unif]

/-- The image of a uniform draw gives each value the size of its fibre, divided by the size of the
sample space. -/
theorem map_unif_apply [Fintype C] [Nonempty C] (f : C → β) (b : β) :
    (unif C).map f b = (cnt fun c => f c = b : ℝ≥0∞) / Fintype.card C := by
  rw [← pr_singleton, pr_map]
  exact pr_unif_eq fun c => f c = b

/-- Equality of distributions from equality of counts. Two quantities computed from uniform draws in
two (possibly different) sample spaces have the same distribution if and only if all fibres have
proportional sizes. -/
theorem map_unif_eq_map_unif_iff
    [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] (f : C → β) (g : D → β) :
    (unif C).map f = (unif D).map g ↔
    ∀ b, cnt (fun c => f c = b) * Fintype.card D = cnt (fun d => g d = b) * Fintype.card C := by
  have key : ∀ b, ((unif C).map f b = (unif D).map g b ↔
      cnt (fun c => f c = b) * Fintype.card D = cnt (fun d => g d = b) * Fintype.card C) := by
    intro b
    rw [map_unif_apply, map_unif_apply,
      ENNReal.div_eq_div_iff (card_ne_zero' D) (card_ne_top' D) (card_ne_zero' C) (card_ne_top' C)]
    constructor
    · intro h
      have h' : Fintype.card D * cnt (fun c => f c = b) =
          Fintype.card C * cnt (fun d => g d = b) := by
        exact_mod_cast h
      rw [mul_comm, h', mul_comm]
    · intro h
      have h' : Fintype.card D * cnt (fun c => f c = b) =
          Fintype.card C * cnt (fun d => g d = b) := by
        rw [mul_comm, h, mul_comm]
      exact_mod_cast h'
  constructor
  · intro h b
    exact (key b).1 (by rw [h])
  · intro h
    exact PMF.ext fun b => (key b).2 (h b)

/-- The image of a uniform draw is uniform if and only if every fibre has |C| / |D| elements. -/
theorem map_unif_eq_unif_iff [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] (f : C → D) :
    (unif C).map f = unif D ↔ ∀ d, cnt (fun c => f c = d) * Fintype.card D = Fintype.card C := by
  have h := map_unif_eq_map_unif_iff f (id : D → D)
  rw [PMF.map_id] at h
  rw [h]
  refine forall_congr' fun d => ?_
  have : cnt (fun d' : D => id d' = d) = 1 := cnt_eq_const d
  rw [this, one_mul]

/-- A bijection maps the uniform distribution to the uniform distribution. -/
theorem map_unif_equiv [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] (e : C ≃ D) :
    (unif C).map e = unif D := by
  rw [map_unif_eq_unif_iff]
  intro d
  have : cnt (fun c => e c = d) = 1 := by
    rw [cnt_equiv e (fun d' => d' = d)]
    exact cnt_eq_const d
  rw [this, one_mul, Fintype.card_congr e]

/-- A uniform pair is a pair of independent uniform draws. -/
theorem unif_prod [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] :
    unif (C × D) = prod (unif C) (unif D) :=
  PMF.ext fun x => by
    obtain ⟨c, d⟩ := x
    rw [prod_apply, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
      PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inl (card_ne_zero' C)) (Or.inl (card_ne_top' C))]

theorem map_fst_unif [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] :
    (unif (C × D)).map Prod.fst = unif C := by
  rw [unif_prod, map_fst_prod]

theorem map_snd_unif [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] :
    (unif (C × D)).map Prod.snd = unif D := by
  rw [unif_prod, map_snd_prod]

/-- Each coordinate of a uniform tuple is uniform. -/
theorem map_eval_unif_pi {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (i₀ : ι) : (unif (∀ i, A i)).map (fun f => f i₀) = unif (A i₀) := by
  rw [map_unif_eq_unif_iff]
  intro a
  rw [cnt_pi_coord i₀ (fun x => x = a), cnt_eq_const, one_mul]

/-- Pr[ all q independent uniform draws have the property P ] = (cnt P / |C|)^q. -/
theorem pr_unif_forall_pow [Fintype C] [Nonempty C] (P : C → Prop) (q : ℕ) :
    pr (unif (Fin q → C)) {I | ∀ j, P (I j)} = ((cnt P : ℝ≥0∞) / Fintype.card C) ^ q := by
  rw [pr_unif_eq, cnt_forall_pow, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow,
    div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

/-- Two rounds with uniform challenges: Pr[bad] ≤ k₁/|C| + k₂/|D| from the two counts. -/
theorem pr_unif_two_rounds_le [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] (P : C × D → Prop)
    (B : C → Prop) (k₁ k₂ : ℕ) (h₁ : cnt B ≤ k₁) (h₂ : ∀ c, ¬ B c → cnt (fun d => P (c, d)) ≤ k₂) :
    pr (unif (C × D)) {x | P x} ≤ (k₁ : ℝ≥0∞) / Fintype.card C + (k₂ : ℝ≥0∞) / Fintype.card D := by
  rw [unif_prod]
  unfold prod
  refine (pr_bind_le_add (unif C) _ {x | P x} {c | B c}
    (ε := (k₂ : ℝ≥0∞) / Fintype.card D) ?_).trans ?_
  · intro c _ hc
    rw [pr_map]
    exact pr_unif_le_of_cnt_le (h₂ c hc)
  · gcongr
    exact pr_unif_le_of_cnt_le h₁

end Unif

end Prob
