-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/TailUnique.lean: at as many distinct points as a tail has entries, the tail is
determined by its values. One statement and its proof. Pure algebra over any field.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  tail_unique        Let pts be a set of r distinct points, and let r coefficients c take the value
                     v x at each point x of pts. Then c is the tail tailFor pts v
                     (Johnson/LinkSim/Tail.lean), entry by entry below r.
  tail_short_fails   A consequence. If entry r - 1 of tailFor pts v is not 0, then no r
                     coefficients whose last entry is 0 take these values.
The proof uses Lagrange.eq_interpolate_of_eval_eq (Mathlib).

How it fits. Johnson/LinkSim/AtText/ShortTail.lean uses it in its negative test.

Limits. With fewer points than r, say n of them, the entries n to r - 1, the last among them, are
not fixed by the values (argued on paper, not proved). The monic polynomial of degree n that is 0 at
the points, times a power of the variable, can be added. An earlier entry can be fixed: entry 0 is
the value at the point 0, where 0 is among the points.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.Tail

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim
open Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- At r distinct points, r coefficients that take the values of v are those of tailFor pts v. -/
theorem tail_unique (pts : Finset F) (v : F → F) (r : ℕ) (hr : pts.card = r) (c : ℕ → F)
    (h : ∀ x ∈ pts, ∑ q ∈ Finset.range r, x ^ q * c q = v x) {q : ℕ} (hq : q < r) :
    c q = tailFor pts v q := by
  have hcoef : ∀ m, (∑ i ∈ Finset.range r, C (c i) * X ^ i : F[X]).coeff m =
      if m < r then c m else 0 := by
    intro m
    simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hdeg : (∑ i ∈ Finset.range r, C (c i) * X ^ i : F[X]).degree < (pts.card : WithBot ℕ) := by
    rw [hr, degree_lt_iff_coeff_zero]
    intro m hm
    rw [hcoef, if_neg (not_lt.mpr hm)]
  have hev : ∀ x ∈ pts, eval (id x) (∑ i ∈ Finset.range r, C (c i) * X ^ i : F[X]) = v x := by
    intro x hx
    rw [← h x hx, eval_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X]
    exact mul_comm _ _
  have e := Lagrange.eq_interpolate_of_eval_eq v (Function.injective_id.injOn) hdeg hev
  unfold tailFor
  rw [← e, hcoef, if_pos hq]

/-- No coefficients whose last is 0 have these values, if tailFor's last is not 0. -/
theorem tail_short_fails (pts : Finset F) (v : F → F) (r : ℕ) (hr : pts.card = r)
    (hne : tailFor pts v (r - 1) ≠ 0) (c : ℕ → F) (hc : c (r - 1) = 0) :
    ¬ ∀ x ∈ pts, ∑ q ∈ Finset.range r, x ^ q * c q = v x := by
  intro h
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exact absurd (tailFor_high pts v (by rw [hr, h0])) hne
    · exact h0
  exact hne ((tail_unique pts v r hr c h (by omega)).symm.trans hc)

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.tail_unique
#print axioms OnBytes.LinkSim.tail_short_fails
