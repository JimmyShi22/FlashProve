-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyTowerOf.lean: the tower of any function that is a polynomial in each variable.

The soundness of the written sumcheck (OnBytes/Slice/KeyPsc.lean) asks for a tower of the summand
(OnBytes/Slice/KeyPscF.lean: Tower). This file builds one for every function f on lists of field
elements that is, in each coordinate, a polynomial with as many coefficients as the coordinate's
weight allows (PolyIn), where each weight is a sum of values at 0 and at 1 with two factors
(Weight.TwoNode). The three kinds of weight of OnBytes/Iop/Psc.lean are of that form: g(0) + g(1),
(1 - z) g(0) + z g(1), and g(0).

The tower (towN) at a list of challenges is the sum of f over the variables that are left (sumN),
each under its weight. Its sum is sumN of f, and its value at a full list of challenges is f.

Polynomials in one variable are Mathlib's here: closure under sums and products comes from there.

Main definitions: Weight.na, Weight.nb, Weight.TwoNode, sumN, towN, PolyIn.

Main theorems: sum_twoNode, plain_twoNode, equality_twoNode, sumN_poly, tower_towN, towN_nil,
towN_full, PolyIn.congr, sumN_congr.

Not claimed. That a given summand is a polynomial in each variable.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyPscF
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false

namespace OnBytes.Slice.PscF
open Prob Cb Polynomial

/-! ## Weights that are sums of values at 0 and 1 -/

/-- The factor of the value at 1. -/
def Weight.nb (w : Weight) : GE := w.moment.getD 1 0

/-- The factor of the value at 0. -/
def Weight.na (w : Weight) : GE := w.moment.getD 0 0 - w.nb

/-- The weight is a sum of the values at 0 and at 1, with two factors: the sums of X, X^2 and so
on are all the same. -/
def Weight.TwoNode (w : Weight) : Prop := ∀ t, 1 ≤ t → t < w.d → w.moment.getD t 0 = w.nb

/-- The value of a polynomial at 0 is its constant coefficient. -/
theorem pv_zero (d : ℕ) (hd : 1 ≤ d) (c : ℕ → GE) : pv d c 0 = c 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  unfold pv
  rw [Finset.sum_range_succ']
  simp

/-- The value of a polynomial at 1 is the sum of its coefficients. -/
theorem pv_one (d : ℕ) (c : ℕ → GE) : pv d c 1 = ∑ t ∈ Finset.range d, c t := by
  unfold pv
  simp

/-- The sum under such a weight. -/
theorem sum_twoNode {w : Weight} (h : w.TwoNode) (hd : 1 ≤ w.d) (c : ℕ → GE) :
    w.sum c = w.na * pv w.d c 0 + w.nb * pv w.d c 1 := by
  rw [pv_zero _ hd, pv_one]
  unfold Weight.sum Weight.na
  obtain ⟨n, hn⟩ : ∃ n, w.d = n + 1 := ⟨w.d - 1, by omega⟩
  rw [hn, Finset.sum_range_succ', Finset.sum_range_succ']
  have hs : ∑ k ∈ Finset.range n, w.moment.getD (k + 1) 0 * c (k + 1) =
      w.nb * ∑ k ∈ Finset.range n, c (k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h (t + 1) (Nat.succ_le_succ (Nat.zero_le t))
      (by rw [hn]; exact Nat.succ_lt_succ (Finset.mem_range.1 ht))]
  rw [hs]
  ring

/-- A member of a list of equal members. -/
theorem getD_cons_replicate (a z : GE) (n t : ℕ) (h1 : 1 ≤ t) (h2 : t < n + 1) :
    (a :: List.replicate n z).getD t 0 = z := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega),
    List.getElem_replicate]

/-- The plain sum is g(0) + g(1). -/
theorem plain_twoNode (d : ℕ) (h : 2 ≤ d) :
    (Weight.plain d).TwoNode ∧ (Weight.plain d).na = 1 ∧ (Weight.plain d).nb = 1 := by
  have hb : (Weight.plain d).nb = 1 :=
    getD_cons_replicate _ _ (d - 1) 1 (Nat.le_refl 1) (by omega)
  refine ⟨fun t h1 h2 => ?_, ?_, hb⟩
  · rw [hb]
    exact getD_cons_replicate _ _ (d - 1) t h1 (by
      have : t < d := h2
      omega)
  · unfold Weight.na
    rw [hb]
    show (1 + 1 : GE) - 1 = 1
    ring

/-- The sum under a factor of the equality polynomial is (1 - z) g(0) + z g(1). -/
theorem equality_twoNode (z : GE) (d : ℕ) (h : 2 ≤ d) :
    (Weight.equality z d).TwoNode ∧ (Weight.equality z d).na = 1 - z ∧
      (Weight.equality z d).nb = z := by
  have hb : (Weight.equality z d).nb = z :=
    getD_cons_replicate _ _ (d - 1) 1 (Nat.le_refl 1) (by omega)
  refine ⟨fun t h1 h2 => ?_, ?_, hb⟩
  · rw [hb]
    exact getD_cons_replicate _ _ (d - 1) t h1 (by
      have : t < d := h2
      omega)
  · unfold Weight.na
    rw [hb]
    rfl

/-! ## The sum over the variables that are left -/

/-- The sum of f over all variables, each under its weight. -/
def sumN : List Weight → (List GE → GE) → GE
  | [], f => f []
  | w :: ws, f => w.na * sumN ws (fun q => f (0 :: q)) + w.nb * sumN ws fun q => f (1 :: q)

/-- The tower of f. -/
def towN : List Weight → (List GE → GE) → List GE → GE
  | [], f, _ => f []
  | w :: ws, f, [] => sumN (w :: ws) f
  | _ :: ws, f, x :: p => towN ws (fun q => f (x :: q)) p

/-- The tower's sum is the sum of f. -/
theorem towN_nil (ws : List Weight) (f : List GE → GE) : towN ws f [] = sumN ws f := by
  cases ws <;> rfl

/-- The tower's value at a full list of challenges is f. -/
theorem towN_full : ∀ (ws : List Weight) (f : List GE → GE) (γ : List GE),
    γ.length = ws.length → towN ws f γ = f γ
  | [], _, [], _ => rfl
  | _ :: ws, f, x :: γ, h => towN_full ws (fun q => f (x :: q)) γ (Nat.succ.inj h)

/-- The sum reads f at lists of as many elements as there are variables. -/
theorem sumN_congr : ∀ (ws : List Weight) {f f' : List GE → GE},
    (∀ q, q.length = ws.length → f q = f' q) → sumN ws f = sumN ws f'
  | [], _, _, h => h [] rfl
  | w :: ws, f, f', h => by
    show w.na * sumN ws (fun q => f (0 :: q)) + w.nb * sumN ws (fun q => f (1 :: q)) =
      w.na * sumN ws (fun q => f' (0 :: q)) + w.nb * sumN ws fun q => f' (1 :: q)
    rw [sumN_congr ws fun q hq => h (0 :: q) (congrArg (· + 1) hq),
      sumN_congr ws fun q hq => h (1 :: q) (congrArg (· + 1) hq)]

/-- f is, in each variable, a polynomial with as many coefficients as the variable's weight
allows, at lists of as many elements as there are variables. -/
def PolyIn : List Weight → (List GE → GE) → Prop
  | [], _ => True
  | w :: ws, f =>
    (∀ q, q.length = ws.length → ∃ p : GE[X], p.natDegree < w.d ∧ ∀ x, f (x :: q) = p.eval x) ∧
      ∀ x, PolyIn ws fun q => f (x :: q)

/-- That property reads f at lists of as many elements as there are variables. -/
theorem PolyIn.congr : ∀ {ws : List Weight} {f f' : List GE → GE},
    (∀ q, q.length = ws.length → f q = f' q) → PolyIn ws f → PolyIn ws f'
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, hf =>
    ⟨fun q hq => by
        obtain ⟨p, hp, he⟩ := hf.1 q hq
        exact ⟨p, hp, fun x => by rw [← h (x :: q) (congrArg (· + 1) hq), he x]⟩,
      fun x => PolyIn.congr (fun q hq => h (x :: q) (congrArg (· + 1) hq)) (hf.2 x)⟩

/-- A sum of polynomials in x, over variables that are left, is a polynomial in x. -/
theorem sumN_poly (d : ℕ) : ∀ (ws : List Weight) (F : GE → List GE → GE),
    (∀ q, q.length = ws.length → ∃ p : GE[X], p.natDegree < d ∧ ∀ x, F x q = p.eval x) →
    ∃ p : GE[X], p.natDegree < d ∧ ∀ x, sumN ws (F x) = p.eval x
  | [], _, h => h [] rfl
  | w :: ws, F, h => by
    obtain ⟨p0, h0, e0⟩ := sumN_poly d ws (fun x q => F x (0 :: q))
      fun q hq => h (0 :: q) (congrArg (· + 1) hq)
    obtain ⟨p1, h1, e1⟩ := sumN_poly d ws (fun x q => F x (1 :: q))
      fun q hq => h (1 :: q) (congrArg (· + 1) hq)
    refine ⟨C w.na * p0 + C w.nb * p1, ?_, fun x => ?_⟩
    · exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt
        (lt_of_le_of_lt (natDegree_C_mul_le _ _) h0) (lt_of_le_of_lt (natDegree_C_mul_le _ _) h1))
    · show w.na * sumN ws (fun q => F x (0 :: q)) + w.nb * sumN ws (fun q => F x (1 :: q)) = _
      rw [e0 x, e1 x, eval_add, eval_mul, eval_mul, eval_C, eval_C]

/-- A polynomial's value, from its coefficients. -/
theorem eval_eq_pv (p : GE[X]) (d : ℕ) (h : p.natDegree < d) (x : GE) :
    p.eval x = pv d (fun t => p.coeff t) x :=
  eval_eq_sum_range' h x

/-- The tower of a function that is a polynomial in each variable. -/
theorem tower_towN : ∀ (ws : List Weight) (f : List GE → GE),
    (∀ w ∈ ws, w.TwoNode ∧ 1 ≤ w.d) → PolyIn ws f → Tower ws (towN ws f)
  | [], _, _, _ => trivial
  | w :: ws, f, hw, hf => by
    obtain ⟨p, hp, he⟩ := sumN_poly w.d ws (fun x q => f (x :: q)) hf.1
    have hw0 := hw w List.mem_cons_self
    refine ⟨⟨fun t => p.coeff t, ?_, fun x => ?_⟩, fun x => ?_⟩
    · rw [sum_twoNode hw0.1 hw0.2, ← eval_eq_pv p w.d hp, ← eval_eq_pv p w.d hp, ← he 0, ← he 1]
      rfl
    · show _ = towN ws (fun q => f (x :: q)) []
      rw [towN_nil, ← eval_eq_pv p w.d hp, ← he x]
    · exact tower_towN ws _ (fun v hv => hw v (List.mem_cons_of_mem _ hv)) (hf.2 x)

end OnBytes.Slice.PscF
