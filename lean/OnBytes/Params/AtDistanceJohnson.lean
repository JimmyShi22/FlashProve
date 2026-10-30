-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/AtDistanceJohnson.lean: a code that the planner reads at a given agreement, where the
source is `.johnson`: what its distance and count enclose, and what the m that is found means.

Where a distance was not made from a code's own m, the planner reads the code at it: `atDistance s c
agree` (OnBytes/Params/Distance.lean). So it reads one of the two codes of a group under the rule
`johnson` (main and mask rows share one distance, which is made from one of the two codes), both
codes of a group under the other rules, and a table whose distances are named in whole positions.
The source is `.johnson` where the test for a third of the distance does not say yes.
The function
then takes the upper end of sqrt rho / eta, where eta is the agreement less sqrt rho (in the other
reading of m: 2 eta for eta), rounded up; m is the larger of that and 3; the count is that of
`johnsonCount` at that m. A result that failed on the way also has the source `.johnson`; its count
is marked bad. `atDistance_johnson`: if the agreement encloses a real number a, the source is
`.johnson` and the count is not marked bad, then the distance encloses 1 - a; the count encloses
`countAt` (OnBytes/Params/JohnsonLaws.lean) at the code's rate, at 1 - a and at the m that was
found; 3 ≤ m; and, with m as printed, a is at least the agreement that belongs to m, sqrt rho (1 + 1
/ m). So, with m as printed, a radius e that is at most (1 - a) n has (m + 1) ^ 2 k n ≤ m ^ 2 (n -
e) ^ 2 at that m (`atDistance_slack`). Beside: a number is at most its value rounded up
(`Binary.le_ceil`), and what a quotient that is not marked bad says of its arguments (`div_good`).

Main theorems: `Binary.le_ceil`, `div_good`, `atDistance_johnson`, `atDistance_slack`.
What is not claimed: what the head of OnBytes/Params/JohnsonLaws.lean does not claim of `countAt`.
Nothing on the list size. Nothing on the slack in the other reading of m: the first three parts of
`atDistance_johnson` hold in both readings, the fourth with m as printed only. That the m that is
found is the least that serves: where sqrt rho / eta is a whole number, rounding can give one more.
Nothing on a table's analysis. For a group's analysis (which code gives the distance, the mask code
read as its repetition, the list size that is added to the mask code's count) see
OnBytes/Params/GroupJohnson.lean. For proofs only; the program, that is the Lean port built from
OnBytes/, does not import this file.

-/
import OnBytes.Params.JohnsonLaws

set_option autoImplicit false

namespace OnBytes.Params
open Bound

namespace Binary

/-- The value is at most the value rounded up to an integer. -/
theorem le_ceil (a : Binary) : a.val ≤ (a.ceil : ℚ) := by
  unfold ceil
  split
  · rename_i h
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
    unfold val
    rw [hk]
    simp
  · rename_i h
    have hv := val_of_neg a h
    rw [hv]
    set k := (-a.e).toNat with hk
    have hP : 0 < 2 ^ k := by positivity
    have hPq : (0 : ℚ) < ((2 ^ k : ℕ) : ℚ) := by exact_mod_cast hP
    simp only
    split
    · rw [div_le_iff₀ hPq]
      have h1 : a.m < 2 ^ k * (a.m / 2 ^ k + 1) := Nat.lt_mul_div_succ a.m hP
      rw [Nat.mul_comm] at h1
      exact_mod_cast h1.le
    · rename_i hb
      have hz : a.m % 2 ^ k = 0 := by
        unfold anyBelow at hb
        simpa using hb
      rw [div_le_iff₀ hPq]
      have h1 : a.m / 2 ^ k * 2 ^ k = a.m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hz)
      exact_mod_cast h1.ge

end Binary

/-- What a quotient that is not marked bad says of its arguments. -/
theorem div_good {a b : Bound} (h : (a / b).bad = false) :
    a.bad = false ∧ b.bad = false ∧ 0 < b.lo.val := by
  have h' : (Bound.div a b).bad = false := h
  unfold Bound.div at h'
  split at h'
  · cases h'
  · rename_i hc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    exact ⟨hc.1.1, hc.1.2, Binary.val_pos _ hc.2⟩

/-- **A code at a given agreement, where `atDistance` gives the source `.johnson` and a count that
is not marked bad**: the distance encloses 1 less what the agreement encloses; the count encloses
the formula at that distance and at the m that was found; 3 ≤ m; and, with m as printed, what the
agreement encloses is at least the agreement that belongs to m. -/
theorem atDistance_johnson {s : Setting} {c : Word} {agree : Bound} {a : ℝ} (ha : EnclR agree a)
    (hs : (atDistance s c agree).source = .johnson)
    (hg : (atDistance s c agree).count.bad = false) :
    EnclR (atDistance s c agree).delta (1 - a) ∧
      EnclR (atDistance s c agree).count
        (countAt c.n c.rho (1 - a) (atDistance s c agree).m) ∧
      3 ≤ (atDistance s c agree).m ∧
      (s.printed = true → c.agreeAt (atDistance s c agree).m true ≤ a) := by
  have hdel : EnclR (Bound.ofWord 1 - agree) (1 - a) := by
    have h := enclR_sub (enclR_ofWord 1) ha
    simpa using h
  unfold atDistance at hs hg ⊢
  dsimp only at hs hg ⊢
  by_cases h1 : (agree.bad || decide (c.n ≤ c.k)) = true
  · rw [if_pos h1] at hg
    cases hg
  · rw [if_neg h1] at hs hg ⊢
    by_cases h2 : (Bound.ofWord 1 - agree).bad = true
    · rw [if_pos h2] at hg
      cases hg
    · rw [if_neg h2] at hs hg ⊢
      by_cases h3 : 3 * ((Bound.ofWord 1 - agree) * Bound.ofNat c.n).hi.floor < c.n - c.k
      · rw [if_pos h3] at hs
        cases hs
      · rw [if_neg h3] at hs hg ⊢
        · by_cases h5 : ((Bound.sqrt (rhoOf c) / (if s.printed = true
                    then agree - Bound.sqrt (rhoOf c)
              else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).bad ||
              decide (2 ^ 64 ≤ (Bound.sqrt (rhoOf c) / (if s.printed = true
                then agree - Bound.sqrt (rhoOf c)
                else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).hi.ceil)) = true
          · rw [if_pos h5] at hg
            cases hg
          · rw [if_neg h5] at hs hg ⊢
            have K : EnclR (Bound.ofWord 1 - agree) (1 - a) ∧
                EnclR (johnsonCount c (rhoOf c) (Bound.ofWord 1 - agree)
                  (max (Bound.sqrt (rhoOf c) / (if s.printed = true
                    then agree - Bound.sqrt (rhoOf c)
                    else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).hi.ceil 3))
                  (countAt c.n c.rho (1 - a)
                    (max (Bound.sqrt (rhoOf c) / (if s.printed = true
                      then agree - Bound.sqrt (rhoOf c)
                      else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).hi.ceil 3)) ∧
                3 ≤ max (Bound.sqrt (rhoOf c) / (if s.printed = true
                    then agree - Bound.sqrt (rhoOf c)
                    else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).hi.ceil 3 ∧
                (s.printed = true → c.agreeAt
                  (max (Bound.sqrt (rhoOf c) / (if s.printed = true
                    then agree - Bound.sqrt (rhoOf c)
                    else Bound.ofWord 2 * (agree - Bound.sqrt (rhoOf c)))).hi.ceil 3) true ≤
                  a) := by
              refine ⟨hdel, enclR_johnsonCount c (enclR_rhoOf c) hdel _, le_max_right _ _, ?_⟩
              intro hp
              simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at h5
              have hq := h5.1
              rw [hp] at hq ⊢
              simp only [if_true] at hq ⊢
              obtain ⟨_, ge, gl⟩ := div_good hq
              have hroot := enclR_sqrt (enclR_rhoOf c)
              have heta := enclR_sub ha hroot
              have hpos : 0 < a - Real.sqrt c.rho :=
                lt_of_lt_of_le (by exact_mod_cast gl) (heta ge).1
              have hqe := (enclR_div hroot heta hq).2
              have hc : (((Bound.sqrt (rhoOf c) / (agree - Bound.sqrt (rhoOf c))).hi.val : ℚ) : ℝ) ≤
                  (((Bound.sqrt (rhoOf c) / (agree - Bound.sqrt (rhoOf c))).hi.ceil : ℕ) : ℝ) := by
                exact_mod_cast Binary.le_ceil _
              set m := max (Bound.sqrt (rhoOf c) / (agree - Bound.sqrt (rhoOf c))).hi.ceil 3 with hm
              have hm3 : 3 ≤ m := le_max_right _ _
              have hmc :
                  (((Bound.sqrt (rhoOf c) / (agree - Bound.sqrt (rhoOf c))).hi.ceil : ℕ) : ℝ) ≤
                    (m : ℝ) := by exact_mod_cast le_max_left _ _
              have hle : Real.sqrt c.rho / (a - Real.sqrt c.rho) ≤ (m : ℝ) :=
                hqe.trans (hc.trans hmc)
              have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
              rw [div_le_iff₀ hpos] at hle
              unfold Word.agreeAt
              simp only [if_true]
              have : Real.sqrt c.rho / (m : ℝ) ≤ a - Real.sqrt c.rho := by
                rw [div_le_iff₀ hm0]
                linarith
              linarith
            dsimp only at hg ⊢
            split at hg
            · rename_i h7
              rw [if_pos h7]
              split at hg
              · cases hg
              · rename_i h6
                rw [if_neg h6]
                exact K
            · rename_i h7
              rw [if_neg h7]
              exact K

/-- **So a radius that is at most what the distance encloses, times the length, is inside the
Johnson radius with the slack that belongs to the m that was found**, with m as printed. -/
theorem atDistance_slack {s : Setting} {c : Word} {agree : Bound} {a : ℝ} {e : ℕ}
    (ha : EnclR agree a) (hs : (atDistance s c agree).source = .johnson)
    (hg : (atDistance s c agree).count.bad = false) (hp : s.printed = true)
    (he : (e : ℝ) ≤ (1 - a) * (c.n : ℝ)) :
    e ≤ c.n ∧ ((atDistance s c agree).m + 1) * ((atDistance s c agree).m + 1) * c.k * c.n ≤
      (atDistance s c agree).m * (atDistance s c agree).m * ((c.n - e) * (c.n - e)) := by
  obtain ⟨_, _, h3, h4⟩ := atDistance_johnson ha hs hg
  have hn : (0 : ℝ) ≤ (c.n : ℝ) := Nat.cast_nonneg _
  refine radius_slack (by omega) (he.trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith [h4 hp]) hn

end OnBytes.Params

#print axioms OnBytes.Params.Binary.le_ceil
#print axioms OnBytes.Params.div_good
#print axioms OnBytes.Params.atDistance_johnson
#print axioms OnBytes.Params.atDistance_slack
