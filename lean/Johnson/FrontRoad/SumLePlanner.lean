-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SumLePlanner.lean: arithmetic on the planner's test for range checks. If, at each
check c of a list, a real number f c is at most 2 ^ −b wherever the planner's routine rangeCheckBits
returns b bits for c, and the planner's test passes at that list (missedInTheChecks returns false),
then the sum of f over the list is at most the planner's bound (sum_le_planner). And the count of
bits natBits for one matrix, in natural numbers with subtraction cut off at 0, is at least the
planner's b at that matrix's check (natBits_ge).
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  sum_le_planner   general in f. The planner's bound is 2 ^ −(sec + the rounded-up logarithms of the
      slots, the batches and the copies), as in missedInTheChecks_sound
      (Johnson/FrontRoad/RangeCheckBits.lean). The proof is that theorem's, with the premise hf
      where it calls rangeCheckBits_sound.
  checkOf, natBits, natBits_ge   checkOf rows columns combinations is the range check with the
      verifier's constants: the bound OnBytes.Model.cellBound = 129
      (OnBytes/Model/VerifyHiding.lean), the range 2 ^ 17, the digits 10 and 8. natBits is 14426 ·
      (2 ^ 17)² / (10000 · columns · 128²) − 1 − clog2 rows − clog2 combinations, in natural
      numbers: the text of windowBits (Johnson/Desc/ProofFile/Honest/K8/Part.lean, whose head names
      the format's page). Where rangeCheckBits (checkOf …) = some b, b is at most natBits. Only "at
      most" is proved. The planner's integer can be below 0, where natBits is cut off at 0; the
      planner returns nothing for some checks; its cap at 2 ^ 30 is not reached at these constants.
  two_pow_natBits_le   so, where the planner returns b, 1 / 2 ^ natBits is at most 2 ^ −b.
  sum_natBits_le_planner, sum_inv_two_pow, sum_natBits_le_planner'   so, where the planner's test
      passes at a list of such checks, the sum of 1 / 2 ^ natBits over the list is at most the
      planner's bound: in the reals, and in the extended non-negative reals, in which a stated share
      has its value.

How it fits. Arithmetic on written numbers: no event, no measure, no prover. It is meant for the sum
of the shares that the honest parts of the smallness test state for their private abort test
(windowShare, Johnson/Desc/ProofFile/Honest/K8/Part.lean); that tie is made in
Johnson/FrontRoad/SharesLePlanner.lean, not here. Words (member, half, part, public and private
abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Lemmas; not one of the
release's goal statements.

Limits.
  No probability is bounded here. That 1 / 2 ^ natBits bounds the chance of any event is not said
      here.
  The planner's bound depends on sec, slots and tableRandom, which are lines of the public files,
      and on oneTime, columnsFirst and batches, which the caller gives. Nothing here ties them to
      any public files. All limits of Johnson/FrontRoad/RangeCheckBits.lean hold.
  The premise on the planner's test fails at the empty list: the planner's test is missed where no
      check is named.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.RangeCheckBits
import OnBytes.Model.VerifyHiding

set_option autoImplicit false

namespace OnBytes.FrontRoad
open OnBytes.Params Real
open OnBytes.Model (lbz t2D0 t2D1)

/-- **Where the planner's test passes at a list of checks, the sum of any term f that is at most 2 ^
−b at each check of the list for which rangeCheckBits returns b is at most the planner's bound.** -/
theorem sum_le_planner (f : RangeCheck → ℝ)
    (l : Lines) (checks : List RangeCheck)
    (hf : ∀ c ∈ checks, ∀ b, rangeCheckBits c = some b → f c ≤ (2 : ℝ) ^ (-(b : ℝ)))
    (oneTime columnsFirst batches : ℕ)
    (h : missedInTheChecks l checks oneTime columnsFirst batches = false) :
    (checks.map f).sum ≤
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
    have hterm : ∀ x ∈ checks.map f, x ≤ (2 : ℝ) ^ (-(least : ℝ)) := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      have hm : rangeCheckBits c ∈ bits.map some := e ▸ List.mem_map_of_mem hc
      obtain ⟨b, hbm, hbe⟩ := List.mem_map.1 hm
      refine (hf c hc b hbe.symm).trans ?_
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

/-- The range check of one matrix, with the verifier's constants. -/
def checkOf (rows columns combinations : ℕ) : RangeCheck :=
  ⟨rows, columns, combinations, OnBytes.Model.cellBound, 2 ^ lbz, (t2D0, t2D1)⟩

/-- The count of bits for one matrix, in natural numbers: subtraction is cut off at 0. It has the
text of windowBits (Johnson/Desc/ProofFile/Honest/K8/Part.lean). -/
def natBits (rows columns combinations : ℕ) : ℕ :=
  14426 * (2 ^ lbz) ^ 2 / (10000 * columns * 128 ^ 2) - 1 - clog2 rows - clog2 combinations

/-- At the verifier's constants the planner's quotient is natBits' first number. -/
theorem rangeQuot_checkOf (rows columns combinations : ℕ) :
    rangeQuot (checkOf rows columns combinations) =
      14426 * (2 ^ lbz) ^ 2 / (10000 * columns * 128 ^ 2) := by
  have e : (OnBytes.Model.cellBound - 1 : ℕ) = 128 := rfl
  unfold rangeQuot checkOf
  dsimp only
  rw [e]
  generalize (2 : ℕ) ^ lbz = t
  have e1 : t * t * 14426 = 14426 * t ^ 2 := by ring
  have e2 : columns * 128 * 128 * 10000 = 10000 * columns * 128 ^ 2 := by ring
  rw [e1, e2]

/-- **Where the planner returns b bits for a matrix's check, b is at most natBits.** -/
theorem natBits_ge (rows columns combinations : ℕ) (b : ℤ)
    (h : rangeCheckBits (checkOf rows columns combinations) = some b) :
    b ≤ (natBits rows columns combinations : ℤ) := by
  obtain ⟨hc, -, -, -, hb⟩ := rangeCheckBits_some _ b h
  have hq := rangeQuot_checkOf rows columns combinations
  have hc' : 0 < columns := hc
  rcases hb with ⟨big, -⟩ | hb
  · exfalso
    rw [hq] at big
    have h1 : 14426 * (2 ^ lbz) ^ 2 / (10000 * columns * 128 ^ 2) ≤
        14426 * (2 ^ lbz) ^ 2 / (10000 * 1 * 128 ^ 2) :=
      Nat.div_le_div_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc')) (by norm_num)
    have h2 : 14426 * (2 ^ lbz) ^ 2 / (10000 * 1 * 128 ^ 2) < 2 ^ 30 := by
      simp only [lbz]
      norm_num
    omega
  · rw [hb, hq]
    show _ ≤ ((14426 * (2 ^ lbz) ^ 2 / (10000 * columns * 128 ^ 2) - 1 - clog2 rows -
      clog2 combinations : ℕ) : ℤ)
    have e1 : (checkOf rows columns combinations).rows = rows := rfl
    have e2 : (checkOf rows columns combinations).combinations = combinations := rfl
    rw [e1, e2]
    omega

/-- So, where the planner returns b, 1 / 2 ^ natBits is at most 2 ^ −b. -/
theorem two_pow_natBits_le (rows columns combinations : ℕ) (b : ℤ)
    (h : rangeCheckBits (checkOf rows columns combinations) = some b) :
    (1 : ℝ) / 2 ^ natBits rows columns combinations ≤ (2 : ℝ) ^ (-(b : ℝ)) := by
  have hb : (b : ℝ) ≤ ((natBits rows columns combinations : ℕ) : ℝ) := by
    exact_mod_cast natBits_ge rows columns combinations b h
  rw [one_div, ← rpow_natCast, ← rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  exact rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Arithmetic on written numbers: no event, no prover. **Where the planner's test passes at a list
of matrices' checks, the sum of 1 / 2 ^ natBits is at most the planner's bound.** -/
theorem sum_natBits_le_planner (l : Lines) (ms : List (ℕ × ℕ × ℕ))
    (oneTime columnsFirst batches : ℕ)
    (h : missedInTheChecks l (ms.map fun x => checkOf x.1 x.2.1 x.2.2) oneTime columnsFirst
      batches = false) :
    (ms.map fun x => (1 : ℝ) / 2 ^ natBits x.1 x.2.1 x.2.2).sum ≤
      (2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) + (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ))) := by
  have g := sum_le_planner (fun c => (1 : ℝ) / 2 ^ natBits c.rows c.columns c.combinations) l
    (ms.map fun x => checkOf x.1 x.2.1 x.2.2)
    (fun c hc b hb => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
      exact two_pow_natBits_le x.1 x.2.1 x.2.2 b hb)
    oneTime columnsFirst batches h
  rw [List.map_map] at g
  exact g

/-- A sum of inverse powers of 2 in the extended non-negative reals is that sum in the reals. -/
theorem sum_inv_two_pow : ∀ ns : List ℕ,
    (ns.map fun n => ((2 : ENNReal) ^ n)⁻¹).sum =
      ENNReal.ofReal (ns.map fun n => (1 : ℝ) / 2 ^ n).sum
  | [] => by simp
  | n :: ns => by
    have h0 : (0 : ℝ) ≤ (ns.map fun n => (1 : ℝ) / 2 ^ n).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
      positivity
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      ENNReal.ofReal_add (by positivity) h0, sum_inv_two_pow ns, one_div,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    norm_num

/-- Arithmetic on written numbers: no event, no prover. **The same in the extended non-negative
reals**, in which a stated share has its value. -/
theorem sum_natBits_le_planner' (l : Lines) (ms : List (ℕ × ℕ × ℕ))
    (oneTime columnsFirst batches : ℕ)
    (h : missedInTheChecks l (ms.map fun x => checkOf x.1 x.2.1 x.2.2) oneTime columnsFirst
      batches = false) :
    (ms.map fun x => ((2 : ENNReal) ^ natBits x.1 x.2.1 x.2.2)⁻¹).sum ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) + (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) := by
  have g := sum_natBits_le_planner l ms oneTime columnsFirst batches h
  have e := sum_inv_two_pow (ms.map fun x => natBits x.1 x.2.1 x.2.2)
  rw [List.map_map, List.map_map] at e
  exact (le_of_eq e).trans (ENNReal.ofReal_le_ofReal g)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.sum_le_planner
#print axioms OnBytes.FrontRoad.checkOf
#print axioms OnBytes.FrontRoad.natBits
#print axioms OnBytes.FrontRoad.rangeQuot_checkOf
#print axioms OnBytes.FrontRoad.natBits_ge
#print axioms OnBytes.FrontRoad.two_pow_natBits_le
#print axioms OnBytes.FrontRoad.sum_natBits_le_planner
#print axioms OnBytes.FrontRoad.sum_inv_two_pow
#print axioms OnBytes.FrontRoad.sum_natBits_le_planner'
