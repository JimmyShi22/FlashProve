-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndIndex.lean: the indices of the smallness test's equations, by the
verifier's own numbers (OnBytes/Model/Tail.lean: stepF, equationsF).

Definitions, statements and proofs. Plain arithmetic.
Main names:
  `eTie tl mu i u`, `eRead tl q u`: the index of a tie's equation and of a read's.
  `tau_le_stepF`, `firstOf_succ`, `firstOf_mono`, `eTie_lt`, `eTie_lt_eRead`, `eRead_lt`: a tie's
    index lies in its matrix's stretch, below every read's; a read's below the number of indices.
Limits: no run and no field element occurs.
-/
import OnBytes.Tie.Pv.Tail.EndLoopsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

/-- The index of the tie's equation for row i of symbols of matrix mu and combination u. -/
def eTie (tl : HTailF2) (mu i u : Nat) : Nat := firstOf tl mu + tl.stepF * i + u

/-- The index of the equation of read number q and combination u. -/
def eRead (tl : HTailF2) (q u : Nat) : Nat := firstOf tl tl.NM + q * tl.stepF + u

theorem tau_le_stepF (tl : HTailF2) : tl.tau ≤ tl.stepF := Slice.le_two_pow_ceilLog2 tl.tau

theorem firstOf_succ (tl : HTailF2) (mu : Nat) :
    firstOf tl (mu + 1) = firstOf tl mu + tl.stepF * 2 ^ clog2 (tl.shp.getD mu {}).mS := by
  simp only [firstOf, Finset.sum_range_succ]

theorem firstOf_mono (tl : HTailF2) {mu nu : Nat} (h : mu ≤ nu) :
    firstOf tl mu ≤ firstOf tl nu := by
  induction nu with
  | zero => have : mu = 0 := by omega
            subst this; exact le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge mu (n + 1) with h1 | h1
    · rw [firstOf_succ]
      exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · have : mu = n + 1 := by omega
      subst this; exact le_refl _

/-- A tie's equation lies in its matrix's own stretch of indices. -/
theorem eTie_lt (tl : HTailF2) (mu i u : Nat) (hi : i < (tl.shp.getD mu {}).mS) (hu : u < tl.tau) :
    firstOf tl mu ≤ eTie tl mu i u ∧ eTie tl mu i u < firstOf tl (mu + 1) := by
  have h1 := tau_le_stepF tl
  have h2 : (tl.shp.getD mu {}).mS ≤ 2 ^ clog2 (tl.shp.getD mu {}).mS := Slice.le_two_pow_ceilLog2 _
  have h3 : tl.stepF * (i + 1) ≤ tl.stepF * 2 ^ clog2 (tl.shp.getD mu {}).mS :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : tl.stepF * (i + 1) = tl.stepF * i + tl.stepF := by ring
  rw [firstOf_succ]
  unfold eTie
  omega

/-- A tie's equation and a read's never have one index. -/
theorem eTie_lt_eRead (tl : HTailF2) (mu i u q u' : Nat) (hmu : mu < tl.NM)
    (hi : i < (tl.shp.getD mu {}).mS) (hu : u < tl.tau) : eTie tl mu i u < eRead tl q u' := by
  have a := eTie_lt tl mu i u hi hu
  have := firstOf_mono tl (show mu + 1 ≤ tl.NM from hmu)
  unfold eRead
  omega

/-- All indices lie below the number that the batching element's round is planned with, less the
plan's
claims: firstOf NM + n stepF for n reads. -/
theorem eRead_lt (tl : HTailF2) (n q u : Nat) (hq : q < n) (hu : u < tl.tau) :
    eRead tl q u < firstOf tl tl.NM + n * tl.stepF := by
  have hs := tau_le_stepF tl
  have h1 : (q + 1) * tl.stepF ≤ n * tl.stepF := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * tl.stepF = q * tl.stepF + tl.stepF := by ring
  unfold eRead
  omega

#print axioms eTie_lt_eRead

end OnBytes.Tie.Pv.Tail.Port
