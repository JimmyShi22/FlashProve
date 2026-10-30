-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  ZKCP/Sep41.lean -- `HasCompletenessError` and `HasRefinedCompletenessError` can be far apart when
  the instance set is infinite and a session's failure depends on the oracle.
  The scheme: instances are the natural numbers, every triple is in R, keys and proofs are empty,
  and V rejects x if and only if f(x) = 0^λ (x written in unary).
  * sep_complete    : completeness error 2^-λ in the sense of `HasCompletenessError`;
  * sep_not_refined : in the refined sense, every α_P < 1 forces α_C ≥ 1: almost surely
                      some instance is rejected, so the one key is bad for almost every f.
  (At λ = 0 the error 2^-λ of `HasCompletenessError` is 1 too.)
  Notation: `u lam` (ZKCP/HashToy.lean): the inverse of the number of digests (`Digest lam`); α_C,
  α_P: elements of ℝ≥0∞, the arguments `αC`, `αP` of `HasRefinedCompletenessError`; a bad key: a
  member of `badKeys` (both: ZKCP/Defs.lean).
-/
import ZKCP.HashToy
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ZKCP

section Sep41
variable (lam : ℕ)

/-- Every triple is in the relation; instances are the natural numbers. -/
def natR : IndexedRelation Unit ℕ Unit Unit where
  rel := fun _ _ _ => True
  pp := fun _ => ()

/-- The instance x as a query string. -/
def pt (x : ℕ) : Str := List.replicate x true

lemma pt_inj {x y : ℕ} (h : pt x = pt y) : x = y := by
  have := congrArg List.length h
  simpa [pt] using this

/-- 0^λ. -/
def zeroD : Digest lam := fun _ => false

/-- V rejects x iff f(x) = 0^λ. -/
def sepArg : Arg lam Unit ℕ Unit Unit Unit Unit where
  C := fun _ => .pure ((), ())
  P := fun _ _ _ => .pure ()
  V := fun _ x _ => .query (pt x) fun d => .pure (decide (d ≠ zeroD lam))

/-- The scheme has completeness error α = 2^-λ (ZKCP/Defs.lean, `HasCompletenessError`). -/
theorem sep_complete : HasCompletenessError natR (sepArg lam) (u lam) := by
  classical
  intro i x w _
  rw [Pr_eq_PrFrom]
  simp only [completenessExp, sessionExp, sepArg, bind_eq, OComp.bind]
  rw [PrFrom_query_miss rfl]
  simp only [PrFrom_pure]
  refine le_trans
    (expect_uniform_le {zeroD lam} _ 0 (fun r => by split_ifs <;> simp) fun r hr => ?_) (by simp)
  rw [if_neg]
  simpa using hr

variable {lam}

/-- Ask f at the instances n-1, ..., 0, up to the first that is rejected; output true iff none of
them is rejected. -/
def scan : ℕ → OComp lam Bool
  | 0 => .pure true
  | n + 1 => .query (pt n) fun d => if d = zeroD lam then .pure false else scan n

lemma expect_le_prob_mul {α : Type} (p : PMF α) (F : α → ℝ≥0∞) (S : Set α) (Y : ℝ≥0∞)
    (h0 : ∀ a, a ∉ S → F a = 0) (h : ∀ a, F a ≤ Y) : expect p F ≤ prob p S * Y := by
  classical
  rw [prob_eq_expect]
  unfold expect
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ S
  · simp only [if_pos ha, mul_one]
    gcongr
    exact h a
  · simp [h0 a ha]

/-- A uniform digest avoids 0^λ with probability 1 - 2^-λ. Stated as a bound on expectations, under
the hypotheses below. -/
lemma expect_uniform_avoid (F : Digest lam → ℝ≥0∞) (Y : ℝ≥0∞)
    (h0 : F (zeroD lam) = 0) (h : ∀ d, F d ≤ Y) :
    expect (PMF.uniformOfFintype (Digest lam)) F ≤ (1 - u lam) * Y := by
  classical
  refine le_trans (expect_le_prob_mul _ F ({zeroD lam}ᶜ) Y (fun d hd => ?_) h) (le_of_eq ?_)
  · have : d = zeroD lam := by simpa using hd
    rw [this, h0]
  · congr 1
    have h3 : prob (PMF.uniformOfFintype (Digest lam)) {zeroD lam} = u lam := by
      rw [prob_eq_expect, expect_uniform]
      simp [u]
    have h4 := prob_add_compl (PMF.uniformOfFintype (Digest lam)) {zeroD lam}
    rw [h3, add_comm] at h4
    have hu : u lam ≠ ⊤ := by simp [u]
    exact ENNReal.eq_sub_of_add_eq hu h4

/-- The first n instances are all accepted with probability at most (1 - 2^-λ)^n, if the cache c
has no entry at any of them. -/
lemma PrFrom_scan_le : ∀ (n : ℕ) (c : Cache lam), (∀ m, m < n → c (pt m) = none) →
    PrFrom c (scan n) {b | b = true} ≤ (1 - u lam) ^ n := by
  classical
  intro n
  induction n with
  | zero => intro c _; simp [scan, PrFrom_pure]
  | succ n ih =>
    intro c hc
    simp only [scan]
    rw [PrFrom_query_miss (hc n (Nat.lt_succ_self n)), pow_succ, mul_comm]
    refine expect_uniform_avoid _ _ ?_ fun d => ?_
    · simp [PrFrom_pure]
    · by_cases hd : d = zeroD lam
      · simp [hd, PrFrom_pure]
      · rw [if_neg hd]
        refine ih _ fun m hm => ?_
        have hne : pt m ≠ pt n := fun e => by have := pt_inj e; omega
        rw [Function.update_of_ne hne]
        exact hc m (Nat.lt_succ_of_lt hm)

/-- If f rejects no instance, the scan says so. -/
lemma scan_of_good (f : Oracle lam) (h : ∀ x, f (pt x) ≠ zeroD lam) :
    ∀ n, PrCoins f (scan n) {b | b = true} = 1 := by
  intro n
  induction n with
  | zero => simp [PrCoins, scan, OComp.run, prob_pure]
  | succ n ih => simpa [PrCoins, scan, OComp.run, h n] using ih

/-- `HasRefinedCompletenessError` fails completely: for every α_P < 1 the committer's error is
1. (Lean: 1 ≤ αC.) -/
theorem sep_not_refined {αC αP : ℝ≥0∞} (hP : αP < 1)
    (h : HasRefinedCompletenessError natR (sepArg lam) αC αP) : 1 ≤ αC := by
  classical
  have hpt : ∀ (n : ℕ) (f : Oracle lam), (1 : ℝ≥0∞) ≤
      PrCoins f ((sepArg lam).C ()) (badKeys natR (sepArg lam) αP () f) +
        PrCoins f (scan n) {b | b = true} := by
    intro n f
    by_cases hb : ((), ()) ∈ badKeys natR (sepArg lam) αP () f
    · have : PrCoins f ((sepArg lam).C ()) (badKeys natR (sepArg lam) αP () f) = 1 := by
        show prob (PMF.pure ((), ())) _ = 1
        rw [prob_pure, if_pos hb]
      rw [this]; exact le_self_add
    · have hg : ∀ x, f (pt x) ≠ zeroD lam := by
        intro x hx
        apply hb
        refine ⟨x, (), trivial, ?_⟩
        have : PrCoins f (sessionExp (sepArg lam) () () x ()) {b | b = false} = 1 := by
          simp [PrCoins, sessionExp, sepArg, OComp.bind, OComp.run, prob_pure, hx]
        rw [this]; exact hP
      rw [scan_of_good f hg n]; exact le_add_self
  have hn : ∀ n : ℕ, (1 : ℝ≥0∞) ≤ αC + (1 - u lam) ^ n := by
    intro n
    calc (1 : ℝ≥0∞) = ∫⁻ _ : Oracle lam, 1 ∂(U lam) := by simp
      _ ≤ ∫⁻ f, (PrCoins f ((sepArg lam).C ()) (badKeys natR (sepArg lam) αP () f) +
            PrCoins f (scan n) {b | b = true}) ∂(U lam) := lintegral_mono (hpt n)
      _ = Pr ((sepArg lam).C ()) (fun f => badKeys natR (sepArg lam) αP () f) +
            Pr (scan n) (fun _ => {b | b = true}) := by
          have hm : Measurable fun f : Oracle lam => PrCoins f (scan n) {b | b = true} :=
            measurable_prob_run (scan n) {b | b = true}
          rw [lintegral_add_right _ hm]; rfl
      _ ≤ αC + (1 - u lam) ^ n := by
          refine add_le_add (h ()) ?_
          rw [Pr_eq_PrFrom]
          exact PrFrom_scan_le n _ fun _ _ => rfl
  have hq : 1 - u lam < 1 := by
    refine ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_
    simp [u]
  have hlim : Tendsto (fun n : ℕ => αC + (1 - u lam) ^ n) atTop (𝓝 (αC + 0)) :=
    tendsto_const_nhds.add (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hn

end Sep41
end ZKCP
