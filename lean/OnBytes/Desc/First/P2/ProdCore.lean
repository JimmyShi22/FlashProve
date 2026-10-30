--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P2/ProdCore.lean: the grand product, one level, as algebra over a field: no text
of a verifier, no bytes, no monad. Definitions, statements and proofs, over Mathlib and the
sumcheck's algebra (OnBytes/Desc/First/P1/SumCore.lean).

A point is a function from the coordinates' numbers to the field; coordinate 0 is the highest bit.
`pcons a y`: the point y with a new coordinate a in front. A level's map is any function on points.
`AffIn m A`: A is affine in each of the first m coordinates. `Step m A B`: A (m coordinates) stands
above B (m + 1 coordinates) in a product tree: both are affine in each coordinate, and on the cube
A y = B (0, y) * B (1, y). `SumsAt w z`: the variable w has three coefficients and is summed with
the equality weights at z. `lvY`: the level's summand with the further variable Y: (B (0, y) + Y
mL) * (B (1, y) + Y mR). `summand`: that summand as a function of the list of challenges, which are
laid at the coordinates L in the order of the rounds; Y's is the last. `place`: the point that the
challenges make. `badLine`, `line_sound`: the step down: if the line through the two hidden end
values meets B (X, r) at the drawn xi, and xi is not the one bad element, both end values are B's.

Limits. Sets are counted; nothing is said of probabilities. The error of the step down is one bad
element of the field (`badLine_card`).
Not claimed: anything on an honest prover or on hiding.

-/
import OnBytes.Desc.First.P1.SumCore
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P2
open Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K]

/-! ### A variable that is summed with the equality weights at z -/

/-- (1 - z) q(0) + z q(1), on polynomials with d coefficients. -/
def ptWt (z : K) (d : ℕ) : Wt K := { d := d, mom := fun i => if i = 0 then 1 else z, psi := 1 }

theorem ptWt_sum (z : K) (d : ℕ) (q : K[X]) (hq : q.natDegree < d) :
    (ptWt z d).sum q = (1 - z) * q.eval 0 + z * q.eval 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have h1 : q.eval 1 = ∑ i ∈ Finset.range (n + 1), q.coeff i := by
    rw [eval_eq_sum_range' hq]
    simp
  have h0 : q.eval 0 = q.coeff 0 := (coeff_zero_eq_eval_zero q).symm
  rw [h1, h0]
  show ∑ i ∈ Finset.range (n + 1), (if i = 0 then (1 : K) else z) * q.coeff i = _
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have e : ∀ i : ℕ, (if i + 1 = 0 then (1 : K) else z) * q.coeff (i + 1) = z * q.coeff (i + 1) :=
    fun i => by rw [if_neg (Nat.succ_ne_zero i)]
  simp only [e, if_true, ← Finset.mul_sum]
  ring

/-- The variable w has three coefficients and is summed with the equality weights at z. Both texts
of
the masked sumcheck have such variables, as different records. -/
def SumsAt (w : Wt K) (z : K) : Prop :=
  w.d = 3 ∧ ∀ q : K[X], q.natDegree < 3 → w.sum q = (1 - z) * q.eval 0 + z * q.eval 1

theorem sumsAt_ptWt (z : K) : SumsAt (ptWt z 3) z := ⟨rfl, fun q hq => ptWt_sum z 3 q hq⟩

/-- The number of coefficients at a place is at most n, if every variable's is. -/
theorem dAt_le (vs : List (Wt K)) (n : ℕ) (h1 : 1 ≤ n) (h : ∀ w ∈ vs, w.d ≤ n) (i : ℕ) :
    dAt vs i ≤ n := by
  unfold dAt
  cases hi : vs[i]? with
  | none => simpa using h1
  | some w => simpa using h w (List.mem_of_getElem? hi)

/-- The product of two lines is a polynomial with three coefficients. -/
theorem two_lines (a0 b0 a1 b1 : K) :
    ∃ q : K[X], q.natDegree < 3 ∧ ∀ x, q.eval x = (a0 + b0 * x) * (a1 + b1 * x) := by
  refine ⟨(C b0 * X + C a0) * (C b1 * X + C a1), ?_, fun x => ?_⟩
  · have h := natDegree_mul_le (p := C b0 * X + C a0) (q := C b1 * X + C a1)
    have h0 := natDegree_linear_le (a := b0) (b := a0)
    have h1 := natDegree_linear_le (a := b1) (b := a1)
    omega
  · simp only [eval_mul, eval_add, eval_C, eval_X]
    ring

/-! ### Points -/

/-- The point y with the new coordinate a in front. -/
def pcons (a : K) (y : ℕ → K) : ℕ → K
  | 0 => a
  | k + 1 => y k

theorem pcons_update (a : K) (y : ℕ → K) (i : ℕ) (c : K) :
    pcons a (Function.update y i c) = Function.update (pcons a y) (i + 1) c := by
  funext k
  cases k with
  | zero => simp [pcons, Function.update_apply]
  | succ k => simp [pcons, Function.update_apply]

theorem pcons_eq_update (a c : K) (y : ℕ → K) : pcons c y = Function.update (pcons a y) 0 c := by
  funext k
  cases k with
  | zero => simp [pcons, Function.update_apply]
  | succ k => simp [pcons, Function.update_apply]

/-- 0 or 1. -/
def Bit (a : K) : Prop := a = 0 ∨ a = 1

/-- A is affine in each of the first m coordinates. -/
def AffIn (m : ℕ) (A : (ℕ → K) → K) : Prop :=
  ∀ (x : ℕ → K) (i : ℕ), i < m → ∃ a b : K, ∀ c, A (Function.update x i c) = a + b * c

/-- **A stands above B in a product tree.** -/
structure Step (m : ℕ) (A B : (ℕ → K) → K) : Prop where
  affA : AffIn m A
  affB : AffIn (m + 1) B
  prod : ∀ y, (∀ k, k < m → Bit (y k)) → A y = B (pcons 0 y) * B (pcons 1 y)

/-! ### The level's summand -/

/-- The summand with the further variable: each end value as value + Y * its mask. -/
def lvY (B : (ℕ → K) → K) (mL mR : K) (y : ℕ → K) (Y : K) : K :=
  (B (pcons 0 y) + Y * mL) * (B (pcons 1 y) + Y * mR)

/-- A summand as a function of the challenges: the challenge of round l is laid at the coordinate
L[l]; the one behind them is the further variable's. -/
def summand (GY : (ℕ → K) → K → K) : List ℕ → (ℕ → K) → List K → K
  | [], x, cs => GY x (cs.headD 0)
  | i :: L, x, cs => summand GY L (Function.update x i (cs.headD 0)) cs.tail

/-- The point that the challenges make. -/
def place (L : List ℕ) (cs : List K) (x : ℕ → K) : ℕ → K :=
  (L.zip cs).foldl (fun y p => Function.update y p.1 p.2) x

theorem summand_place (GY : (ℕ → K) → K → K) (β : K) : ∀ (L : List ℕ) (r : List K) (x : ℕ → K),
    r.length = L.length → summand GY L x (r ++ [β]) = GY (place L r x) β
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | i :: L, c :: r, x, h => by
    have ih := summand_place GY β L r (Function.update x i c) (by simpa using h)
    show summand GY L (Function.update x i c) (r ++ [β]) = _
    rw [ih]
    rfl

/-! ### The step down -/

open Classical in
/-- The one element at which a wrong pair of end values can pass the line. B0, B1: the map below at
(0, r) and (1, r). vL, vR: the two hidden end values. -/
def badLine (B0 B1 vL vR : K) : Finset K :=
  if vR - B1 = vL - B0 then ∅ else {(vL - B0) / ((vL - B0) - (vR - B1))}

theorem badLine_card (B0 B1 vL vR : K) : (badLine B0 B1 vL vR).card ≤ 1 := by
  unfold badLine
  split <;> simp

/-- **The step down is sound but for one element.** -/
theorem line_sound {m : ℕ} {B : (ℕ → K) → K} (hB : AffIn (m + 1) B) (r : ℕ → K) (vL vR xi : K)
    (hx : xi ∉ badLine (B (pcons 0 r)) (B (pcons 1 r)) vL vR)
    (he : (1 - xi) * vL + xi * vR = B (pcons xi r)) :
    vL = B (pcons 0 r) ∧ vR = B (pcons 1 r) := by
  obtain ⟨a, b, e⟩ := hB (pcons 0 r) 0 (by omega)
  have e' : ∀ c, B (pcons c r) = a + b * c := fun c => by
    rw [pcons_eq_update 0 c r]
    exact e c
  rw [e' 0, e' 1] at hx ⊢
  rw [e' xi] at he
  by_cases h : vR - (a + b * 1) = vL - (a + b * 0)
  · have h0 : vL - (a + b * 0) = 0 := by linear_combination he - xi * h
    exact ⟨by linear_combination h0, by linear_combination h + h0⟩
  · exfalso
    apply hx
    unfold badLine
    rw [if_neg h, Finset.mem_singleton]
    have hne : (vL - (a + b * 0)) - (vR - (a + b * 1)) ≠ 0 := fun e0 =>
      h (by linear_combination -e0)
    rw [eq_div_iff hne]
    linear_combination -he

end OnBytes.Desc.First.P2
