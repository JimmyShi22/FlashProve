-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/RangeCheckBits.lean: the number of bits that the planner's test on the range
checks computes (OnBytes/Params/Gate.lean) is never more than minus the binary logarithm of the real
expression that it stands for.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
The planner: the routines that size public files and refuse those that miss a condition. The
expression of one check c is rangeTerm c = rows · combinations · 2 · exp(−range² / (columns · (bound
− 1)²)), a real number.
rangeCheckBits_sound: if rangeCheckBits c returns the whole number b, then rangeTerm c ≤ 2 ^ (−b).
So the routine's rounding never claims more bits than the real expression gives. b can be negative;
the bound then exceeds 1 and says nothing.
missedInTheChecks_sound: if the planner's test passes (missedInTheChecks returns false) at the lines
l of the public files, a list of checks and the caller's numbers oneTime, columnsFirst and batches,
then the sum of rangeTerm over the checks is at most 2 ^ −(sec + clog2 slots + clog2 (max 1 batches)
+ clog2 copies). Here sec is the target in bits and slots the most requests in a batch, both lines
of l. batches are the batches that a stored copy covers. copies are the stored copies as the planner
counts them (plannedCopies). clog2 is the planner's rounded-up binary logarithm.
allRequests_sound: under the same premise, slots · max 1 batches · copies times that sum is at most
2 ^ −sec.

  self_le_pow_clog2   n ≤ 2 ^ clog2 n. The same statement, for the twin definition in
      Johnson/Desc/Kinds/HeadParts.lean, is le_two_pow_clog2 in
      Johnson/Desc/Kinds/Law/FromLookup.lean.
  rangeQuot, rangeExp, rangeTerm, plannedCopies   the whole number that rangeCheckBits computes as
      bits; the exponent; the expression; the planner's count of copies. Each is a part of the
      planner's text, or of the expression, under a name.
  rangeCheckBits_some   four of the tests that rangeCheckBits makes where it returns a number, those
      that the proofs use, and which of its two values that number is.
  rangeQuot_le, bits_mul_log_le, exp_neg_le_two_rpow   where columns > 0 and bound ≥ 2: rangeQuot is
      at most 1.4426 times the exponent, and times log 2 it is at most the exponent; exp(−x) ≤ 2 ^
      (−y) where y · log 2 ≤ x.
  allOfFrom_some, leastOf_le   where the planner's allOf returns a list every entry held a value;
      the least of a list is at most each entry.

How it fits. The docstring of rangeCheckBits says of its bound: «The derivation is given above
range_check_bits in blocks/frame/hiding_conditions.h and is not proved here.» This file proves the
arithmetic half of that derivation, and of the planner's sum over checks and requests. The other
half is that rangeTerm bounds the chance that an honest prover fails one range check. For one matrix
that is pr_win_le (Prob/Window.lean) with t = range, n₂ = columns and b = bound − 1: its count of
entries is rows · combinations and its term is 2 · exp(−t² / (n₂ · b²)), so its right side is
rangeTerm, read as an extended non-negative real (ENNReal.ofReal). For the range proof's matrices,
each at its own number of columns, it is pr_winOf_le with pr_leaves_sum
(Johnson/Desc/K8/Honest/WindowLawEach.lean), at range = 2 ^ 17 and bound = 129. It is not
windowBound (Johnson/Desc/K8/Honest/WindowLaw.lean), which uses one number of columns for all
matrices of a place and can be larger. The two halves are not joined here. At the cap of
rangeCheckBits (rangeQuot reaches 2 ^ 30) the proof uses that rows are below 2 ^ 40 and combinations
below 2 ^ 16, which the routine tests, and that 1.4426 · log 2 is a little below 1. A lemma toward
the condition HidSmall (E2E/BridgePrivacy.lean); not one of the release's goal statements.

Limits.
  It is arithmetic alone. It says nothing of a probability, of a prover, or of what is hidden.
  Joining the two halves needs, besides the lemmas named above, that every cell of the checked
      matrix is at most bound − 1 in absolute value (the verifier's list of checks puts bound = 129,
      and nothing there tests it: OnBytes/Model/VerifyHiding.lean), that the checks which the
      planner is handed are the protocol's own matrices, and that the combinations are the
      verifier's uniform draws. It also needs that public files in scope pass the planner's test.
  The expression is the planner's bound on how often an honest prover fails a range check. That it
      bounds that chance is the other half, not proved here. 2 ^ −sec is no security level here: sec
      is the public files' target for soundness (Lines.sec, OnBytes/Params/File.lean), which the
      planner reuses as its target for this sum.
  The bound of missedInTheChecks_sound depends on sec, slots and tableRandom, which are lines of the
      public files, and on oneTime, columnsFirst and batches, which the caller hands in. Nothing
      here says that these three are the protocol's, or that slots · batches · copies is the number
      of requests that a key serves. The bound is 2 ^ −sec where slots, batches and copies are each
      at most 1, and smaller where one of them is 2 or more.
Terms: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.
-/
import OnBytes.Params.Gate
import Prob.Window

set_option autoImplicit false

namespace OnBytes.FrontRoad
open OnBytes.Params Real

/-- n ≤ 2 ^ clog2 n. -/
theorem self_le_pow_clog2 (n : ℕ) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · rename_i h
    simpa using h
  · have h1 : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) := Nat.lt_log2_self
    omega

/-- The whole number that rangeCheckBits computes as bits: range² · 14426 / (columns · (bound − 1)²
· 10000), rounded down. -/
def rangeQuot (c : RangeCheck) : ℕ :=
  c.range * c.range * 14426 / (c.columns * (c.bound - 1) * (c.bound - 1) * 10000)

/-- Four of the tests that rangeCheckBits makes where it returns a number, those that the proofs
use, and which of its two values that number is. -/
theorem rangeCheckBits_some (c : RangeCheck) (b : ℤ) (h : rangeCheckBits c = some b) :
    0 < c.columns ∧ 2 ≤ c.bound ∧ c.rows < 2 ^ 40 ∧ c.combinations < 2 ^ 16 ∧
      ((2 ^ 30 ≤ rangeQuot c ∧ b = 2 ^ 30) ∨
        b = (rangeQuot c : ℤ) - 1 - (clog2 c.rows : ℤ) - (clog2 c.combinations : ℤ)) := by
  unfold rangeCheckBits at h
  dsimp only at h
  split at h
  · cases h
  · rename_i g1
    split at h
    · cases h
    · rename_i g2
      split at h
      · cases h
      · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_lt, not_le] at g1 g2
        obtain ⟨⟨⟨⟨-, hc⟩, -⟩, hb⟩, -⟩ := g1
        obtain ⟨⟨⟨⟨-, -⟩, -⟩, hr⟩, hk⟩ := g2
        refine ⟨Nat.pos_of_ne_zero hc, hb, hr, hk, ?_⟩
        split at h
        · rename_i g4
          exact Or.inl ⟨g4, (Option.some.inj h).symm⟩
        · exact Or.inr (Option.some.inj h).symm

/-- The exponent of the tail bound. Meant where columns > 0 and bound ≥ 2, which rangeCheckBits
tests; elsewhere the division by 0 gives 0. -/
noncomputable def rangeExp (c : RangeCheck) : ℝ :=
  (c.range : ℝ) ^ 2 / ((c.columns : ℝ) * ((c.bound - 1 : ℕ) : ℝ) ^ 2)

/-- Where columns > 0 and bound ≥ 2, rangeQuot is at most 1.4426 times the exponent. -/
theorem rangeQuot_le (c : RangeCheck) (hc : 0 < c.columns) (hb : 2 ≤ c.bound) :
    (rangeQuot c : ℝ) ≤ 1.4426 * rangeExp c := by
  have hB : 0 < c.bound - 1 := by omega
  have hD : (0 : ℝ) < (c.columns : ℝ) * ((c.bound - 1 : ℕ) : ℝ) ^ 2 := by positivity
  have h1 : rangeQuot c * (c.columns * (c.bound - 1) * (c.bound - 1) * 10000) ≤
      c.range * c.range * 14426 := Nat.div_mul_le_self _ _
  have h2 : (rangeQuot c : ℝ) *
      ((c.columns : ℝ) * ((c.bound - 1 : ℕ) : ℝ) * ((c.bound - 1 : ℕ) : ℝ) * 10000) ≤
      (c.range : ℝ) * (c.range : ℝ) * 14426 := by exact_mod_cast h1
  unfold rangeExp
  rw [mul_div_assoc', le_div_iff₀ hD]
  nlinarith [h2]

/-- Where columns > 0 and bound ≥ 2, rangeQuot times log 2 is at most the exponent. -/
theorem bits_mul_log_le (c : RangeCheck) (hc : 0 < c.columns) (hb : 2 ≤ c.bound) :
    (rangeQuot c : ℝ) * log 2 ≤ rangeExp c := by
  have h := rangeQuot_le c hc hb
  have hl := log_two_lt_d9
  have hl0 : 0 < log 2 := log_pos (by norm_num)
  have hq : (0 : ℝ) ≤ (rangeQuot c : ℝ) := Nat.cast_nonneg _
  have hx : 0 ≤ rangeExp c := by
    unfold rangeExp
    positivity
  calc (rangeQuot c : ℝ) * log 2 ≤ (1.4426 * rangeExp c) * log 2 :=
        mul_le_mul_of_nonneg_right h hl0.le
    _ ≤ (1.4426 * rangeExp c) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hl.le (by positivity)
    _ ≤ rangeExp c := by nlinarith [hx]

/-- exp (−x) ≤ 2 ^ (−y) where y · log 2 ≤ x. -/
theorem exp_neg_le_two_rpow (x y : ℝ) (h : y * log 2 ≤ x) : exp (-x) ≤ (2 : ℝ) ^ (-y) := by
  rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply exp_le_exp.2
  linarith

/-- **Where rangeCheckBits returns b, the expression is at most 2 ^ (−b).** The left side is
rangeTerm c, written out. -/
theorem rangeCheckBits_sound (c : RangeCheck) (b : ℤ) (h : rangeCheckBits c = some b) :
    (c.rows : ℝ) * (c.combinations : ℝ) * (2 * exp (-rangeExp c)) ≤ (2 : ℝ) ^ (-(b : ℝ)) := by
  obtain ⟨hc, hb, hr, hk, hcase⟩ := rangeCheckBits_some c b h
  have two : (0 : ℝ) < 2 := by norm_num
  have hexp : 0 ≤ exp (-rangeExp c) := (exp_pos _).le
  rcases hcase with ⟨hq, rfl⟩ | rfl
  · -- the cap
    have hq' : ((2 : ℝ) ^ 30) ≤ (rangeQuot c : ℝ) := by exact_mod_cast hq
    have hx : ((2 : ℝ) ^ 30 + 57) * log 2 ≤ rangeExp c := by
      have h1 := rangeQuot_le c hc hb
      have hl := log_two_lt_d9
      have hl0 : 0 < log 2 := log_pos (by norm_num)
      nlinarith [h1, hq', hl, hl0]
    have he := exp_neg_le_two_rpow (rangeExp c) ((2 : ℝ) ^ 30 + 57) hx
    have hr' : (c.rows : ℝ) ≤ (2 : ℝ) ^ (40 : ℝ) := by
      rw [show ((40 : ℝ)) = ((40 : ℕ) : ℝ) by norm_num, rpow_natCast]
      exact_mod_cast hr.le
    have hk' : (c.combinations : ℝ) ≤ (2 : ℝ) ^ (16 : ℝ) := by
      rw [show ((16 : ℝ)) = ((16 : ℕ) : ℝ) by norm_num, rpow_natCast]
      exact_mod_cast hk.le
    have e : (2 : ℝ) ^ (-(((2 ^ 30 : ℤ) : ℤ) : ℝ)) =
        (2 : ℝ) ^ (40 : ℝ) * (2 : ℝ) ^ (16 : ℝ) * ((2 : ℝ) ^ (1 : ℝ) *
          (2 : ℝ) ^ (-((2 : ℝ) ^ 30 + 57))) := by
      rw [← rpow_add two, ← rpow_add two, ← rpow_add two]
      congr 1
      push_cast
      ring
    rw [e, rpow_one]
    have p40 : (0 : ℝ) ≤ (2 : ℝ) ^ (40 : ℝ) := (rpow_pos_of_pos two _).le
    exact mul_le_mul (mul_le_mul hr' hk' (Nat.cast_nonneg _) p40)
      (mul_le_mul_of_nonneg_left he two.le) (by positivity) (by positivity)
  · -- below the cap
    have he := exp_neg_le_two_rpow (rangeExp c) (rangeQuot c : ℝ) (bits_mul_log_le c hc hb)
    have hr' : (c.rows : ℝ) ≤ (2 : ℝ) ^ ((clog2 c.rows : ℕ) : ℝ) := by
      rw [rpow_natCast]
      exact_mod_cast self_le_pow_clog2 c.rows
    have hk' : (c.combinations : ℝ) ≤ (2 : ℝ) ^ ((clog2 c.combinations : ℕ) : ℝ) := by
      rw [rpow_natCast]
      exact_mod_cast self_le_pow_clog2 c.combinations
    have e : (2 : ℝ) ^ (-((((rangeQuot c : ℤ) - 1 - (clog2 c.rows : ℤ) -
        (clog2 c.combinations : ℤ) : ℤ)) : ℝ)) =
        (2 : ℝ) ^ ((clog2 c.rows : ℕ) : ℝ) * (2 : ℝ) ^ ((clog2 c.combinations : ℕ) : ℝ) *
          ((2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(rangeQuot c : ℝ))) := by
      rw [← rpow_add two, ← rpow_add two, ← rpow_add two]
      congr 1
      push_cast
      ring
    rw [e, rpow_one]
    have pr : (0 : ℝ) ≤ (2 : ℝ) ^ ((clog2 c.rows : ℕ) : ℝ) := (rpow_pos_of_pos two _).le
    exact mul_le_mul (mul_le_mul hr' hk' (Nat.cast_nonneg _) pr)
      (mul_le_mul_of_nonneg_left he two.le) (by positivity) (by positivity)

/-! ## All checks of a request -/

/-- The expression of one check: rows · combinations · 2 · exp (−exponent). Meant where columns > 0
and bound ≥ 2, as rangeExp. -/
noncomputable def rangeTerm (c : RangeCheck) : ℝ :=
  (c.rows : ℝ) * (c.combinations : ℝ) * (2 * exp (-rangeExp c))

/-- Where allOfFrom returns a list, every entry held a value, and the list is what was seen, in
order, followed by these values. -/
theorem allOfFrom_some {α : Type} : ∀ (l : List (Option α)) (seen out : List α),
    allOfFrom seen l = some out → ∃ vs, l = vs.map some ∧ out = seen.reverse ++ vs
  | [], seen, out, h => ⟨[], rfl, by
      have h' : some seen.reverse = some out := h
      rw [List.append_nil]
      exact (Option.some.inj h').symm⟩
  | none :: _, _, _, h => by cases h
  | some a :: l, seen, out, h => by
      obtain ⟨vs, e, o⟩ := allOfFrom_some l (a :: seen) out h
      refine ⟨a :: vs, by rw [e]; rfl, ?_⟩
      rw [o, List.reverse_cons, List.append_assoc]
      rfl

/-- The least of a list of whole numbers and a start value is at most the start value and at most
each entry. -/
theorem leastOf_le : ∀ (l : List ℤ) (a : ℤ),
    l.foldl min a ≤ a ∧ ∀ b ∈ l, l.foldl min a ≤ b
  | [], a => ⟨le_rfl, fun _ h => by cases h⟩
  | x :: l, a => by
      obtain ⟨h1, h2⟩ := leastOf_le l (min a x)
      refine ⟨h1.trans (min_le_left _ _), fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact h1.trans (min_le_right _ _)
      · exact h2 b hb'

/-- The number of stored copies that the planner counts. -/
def plannedCopies (l : Lines) (oneTime columnsFirst : ℕ) : ℕ :=
  1 + (l.tableRandom - min l.tableRandom oneTime) / max 1 columnsFirst

/-- **Where the planner's test on the range checks passes (missedInTheChecks returns false), the sum
of the checks' expressions is at most 2 ^ −(sec + the rounded-up logarithms of the slots, the
batches and the copies).** -/
theorem missedInTheChecks_sound (l : Lines) (checks : List RangeCheck)
    (oneTime columnsFirst batches : ℕ)
    (h : missedInTheChecks l checks oneTime columnsFirst batches = false) :
    (checks.map rangeTerm).sum ≤
      (2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) + (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ))) := by
  have two : (0 : ℝ) < 2 := by norm_num
  unfold missedInTheChecks at h
  split at h
  · cases h
  · rename_i bits hb
    dsimp only at h
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h
    obtain ⟨-, hle⟩ := h
    obtain ⟨vs, e, o⟩ := allOfFrom_some _ [] bits hb
    have o' : bits = vs := by simpa using o
    subst o'
    have hmin := (leastOf_le bits (2 ^ 30)).2
    generalize List.foldl min (2 ^ 30) bits = least at hle hmin
    have hterm : ∀ x ∈ checks.map rangeTerm, x ≤ (2 : ℝ) ^ (-(least : ℝ)) := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      have hm : rangeCheckBits c ∈ bits.map some := e ▸ List.mem_map_of_mem hc
      obtain ⟨b, hbm, hbe⟩ := List.mem_map.1 hm
      refine (rangeCheckBits_sound c b hbe.symm).trans ?_
      apply rpow_le_rpow_of_exponent_le (by norm_num)
      have : (least : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmin b hbm
      linarith
    have hsum := List.sum_le_card_nsmul _ _ hterm
    rw [List.length_map, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have hlen : (checks.length : ℝ) ≤ (2 : ℝ) ^ ((clog2 checks.length : ℕ) : ℝ) := by
      rw [rpow_natCast]
      exact_mod_cast self_le_pow_clog2 checks.length
    refine (mul_le_mul_of_nonneg_right hlen (rpow_pos_of_pos two _).le).trans ?_
    rw [← rpow_add two]
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    have hle' : ((l.sec : ℤ) : ℝ) ≤
        ((least - (clog2 checks.length : ℤ) - (clog2 l.slots : ℤ) - (clog2 (max 1 batches) : ℤ) -
          (clog2 (plannedCopies l oneTime columnsFirst) : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hle
    push_cast at hle'
    linarith

/-- **Times slots · max 1 batches · copies, the planner's count of the requests that a key can
serve, the sum is at most 2 ^ −sec.** That this product is the number of requests that a key serves
is not said here. -/
theorem allRequests_sound (l : Lines) (checks : List RangeCheck)
    (oneTime columnsFirst batches : ℕ)
    (h : missedInTheChecks l checks oneTime columnsFirst batches = false) :
    ((l.slots : ℝ) * ((max 1 batches : ℕ) : ℝ) * (plannedCopies l oneTime columnsFirst : ℝ)) *
      (checks.map rangeTerm).sum ≤ (2 : ℝ) ^ (-(l.sec : ℝ)) := by
  have two : (0 : ℝ) < 2 := by norm_num
  have h1 := missedInTheChecks_sound l checks oneTime columnsFirst batches h
  have pw : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ ((clog2 n : ℕ) : ℝ) := fun n => by
    rw [rpow_natCast]
    exact_mod_cast self_le_pow_clog2 n
  have pos : ∀ y : ℝ, (0 : ℝ) ≤ (2 : ℝ) ^ y := fun y => (rpow_pos_of_pos two y).le
  have hN : (l.slots : ℝ) * ((max 1 batches : ℕ) : ℝ) * (plannedCopies l oneTime columnsFirst : ℝ) ≤
      (2 : ℝ) ^ ((clog2 l.slots : ℕ) : ℝ) * (2 : ℝ) ^ ((clog2 (max 1 batches) : ℕ) : ℝ) *
        (2 : ℝ) ^ ((clog2 (plannedCopies l oneTime columnsFirst) : ℕ) : ℝ) :=
    mul_le_mul (mul_le_mul (pw _) (pw _) (Nat.cast_nonneg _) (pos _)) (pw _) (Nat.cast_nonneg _)
      (mul_nonneg (pos _) (pos _))
  have hs : 0 ≤ (checks.map rangeTerm).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    unfold rangeTerm
    positivity
  refine (mul_le_mul hN h1 hs (mul_nonneg (mul_nonneg (pos _) (pos _)) (pos _))).trans
    (le_of_eq ?_)
  rw [← rpow_add two, ← rpow_add two, ← rpow_add two]
  congr 1
  ring

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.self_le_pow_clog2
#print axioms OnBytes.FrontRoad.rangeQuot
#print axioms OnBytes.FrontRoad.rangeCheckBits_some
#print axioms OnBytes.FrontRoad.rangeExp
#print axioms OnBytes.FrontRoad.rangeQuot_le
#print axioms OnBytes.FrontRoad.bits_mul_log_le
#print axioms OnBytes.FrontRoad.exp_neg_le_two_rpow
#print axioms OnBytes.FrontRoad.rangeCheckBits_sound
#print axioms OnBytes.FrontRoad.rangeTerm
#print axioms OnBytes.FrontRoad.allOfFrom_some
#print axioms OnBytes.FrontRoad.leastOf_le
#print axioms OnBytes.FrontRoad.plannedCopies
#print axioms OnBytes.FrontRoad.missedInTheChecks_sound
#print axioms OnBytes.FrontRoad.allRequests_sound
