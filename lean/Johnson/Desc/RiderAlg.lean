-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/RiderAlg.lean: one draw, many riders: the algebra alone. It imports Mathlib's
polynomials and nothing of this library, so that any file can call it.

A RIDER is a polynomial in the element x that a verifier draws. If each rider of a list has degree
at most δ, the BAD values of x are the roots of the FIRST rider that is not the zero polynomial: at
most δ values: the largest degree, NOT the sum over the riders (`badRiders_card_le`). At every other
x: if all riders vanish at x, all riders are the zero polynomial (`riders_back`). A bad value is a
root of a rider that is not zero (`mem_badRiders`).

The maximum is right for this state alone: "some equation that is alive is false at the one datum to
which the prover is bound". It is not right over several events that each rescue the same false
equation, nor over several candidates for the datum.

No basis is fixed. `eqk a b` is the rider (1 - x) a + x b, the pair of an equality kernel, with its
value, its degree, and: it is the zero polynomial only if a and b are 0.

Where it is used: Johnson/Desc/RiderLaw.lean (the law of the rounds of a block that hears).

-/
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc
open Polynomial

section Riders
variable (K : Type) [Field K]

open Classical in
/-- **The bad values of a draw**: the roots of the first rider that is not the zero polynomial; none
if there is no such rider. -/
def badRiders (riders : List K[X]) : Finset K :=
  match riders.find? fun q => decide (q ≠ 0) with
  | some q => q.roots.toFinset
  | none => ∅

/-- At most δ values are bad: the largest degree, not the sum. -/
theorem badRiders_card_le (riders : List K[X]) (δ : ℕ) (h : ∀ q ∈ riders, q.natDegree ≤ δ) :
    (badRiders K riders).card ≤ δ := by
  classical
  unfold badRiders
  cases hf : riders.find? fun q => decide (q ≠ 0) with
  | none => simp
  | some q =>
    exact (Multiset.toFinset_card_le _).trans
      ((card_roots' q).trans (h q (List.mem_of_find?_eq_some hf)))

/-- A bad value is a root of a rider that is not the zero polynomial. -/
theorem mem_badRiders {riders : List K[X]} {c : K} (h : c ∈ badRiders K riders) :
    ∃ q ∈ riders, q ≠ 0 ∧ q.eval c = 0 := by
  classical
  unfold badRiders at h
  cases hf : riders.find? fun q => decide (q ≠ 0) with
  | none => rw [hf] at h; simp at h
  | some q =>
    rw [hf] at h
    have hq : q ≠ 0 := by simpa using List.find?_some hf
    exact ⟨q, List.mem_of_find?_eq_some hf, hq, ((mem_roots hq).1 (Multiset.mem_toFinset.1 h))⟩

/-- **Off the bad values: if all riders vanish, all riders are the zero polynomial.** -/
theorem riders_back (riders : List K[X]) (c : K) (hc : c ∉ badRiders K riders)
    (hv : ∀ q ∈ riders, q.eval c = 0) : ∀ q ∈ riders, q = 0 := by
  classical
  intro q hq
  by_contra hne
  cases hf : riders.find? fun q => decide (q ≠ 0) with
  | none =>
    have := List.find?_eq_none.1 hf q hq
    simp [hne] at this
  | some u =>
    apply hc
    unfold badRiders
    rw [hf]
    have hu : u ≠ 0 := by simpa using List.find?_some hf
    exact Multiset.mem_toFinset.2 ((mem_roots hu).2 (hv u (List.mem_of_find?_eq_some hf)))

/-- A rider in the pair (1 - x, x) of an equality kernel: (1 - x) a + x b. -/
def eqk (a b : K) : K[X] := C (b - a) * X + C a

theorem eqk_eval (a b c : K) : (eqk K a b).eval c = (1 - c) * a + c * b := by
  simp only [eqk, eval_add, eval_mul, eval_C, eval_X]
  ring

theorem eqk_natDegree_le (a b : K) : (eqk K a b).natDegree ≤ 1 := natDegree_linear_le

theorem eqk_eq_zero {a b : K} (h : eqk K a b = 0) : a = 0 ∧ b = 0 := by
  have h0 := eqk_eval K a b 0
  have h1 := eqk_eval K a b 1
  rw [h, eval_zero] at h0 h1
  constructor
  · simpa using h0.symm
  · simpa using h1.symm

end Riders

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.badRiders_card_le
#print axioms VerifiableInference.Desc.mem_badRiders
#print axioms VerifiableInference.Desc.riders_back
#print axioms VerifiableInference.Desc.eqk_eval
#print axioms VerifiableInference.Desc.eqk_natDegree_le
#print axioms VerifiableInference.Desc.eqk_eq_zero
