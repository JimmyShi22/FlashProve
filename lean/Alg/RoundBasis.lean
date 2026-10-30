-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/RoundBasis.lean: three ways to send the polynomial of a sum-check round as scalars, by explicit
formulas, with soundness and completeness.

A protocol text of the programs, not in this repository: SC3 and SCD.

A round of degree e + 1 sends e + 1 scalars. With the round's equation Λ(h) = w(0) h(0) + w(1) h(1)
= c (c the running claim) they determine a polynomial h of degree at most e + 1; the next running
claim is h(r).
 1. `Basis`: data only, explicit functions in the field: the coefficients of the running claim and
    of the scalars in the next running claim (the verifier's side), and the honest scalars (the
    prover's side). `Basis.next`, the verifier's recurrence, is linear in the running claim and in
    the scalars, so it applies to affine forms too. No polynomial is in these data: Mathlib's
    polynomials are built with choice, and a verifier or prover has to be given by formulas.
    `Basis.Sound`, `Basis.Complete`: the two properties (those of `RoundFormat` in
    Alg/SumCheck.lean, which is stated with polynomials). `Basis.count_bad_le`: for a sound basis
    over a finite field, if the summand has degree at most d j in each variable j (`hg`) and d i ≤ e
    + 1 for the round's variable i (`hD`), at most e + 1 challenges of a round are bad; w(1) ≠ 0 is
    part of the counted predicate.
    `Basis.next_roundPoly`: the honest round.
 2. `Basis.coeff` sends the value at 0 and the coefficients of X^2, .., X^(e+1). Sound if w(1) ≠ 0.
 3. `Basis.values` sends the values at 0, 2, 3, .., e + 1: the programs' SCD.
    `Basis.next_values_plain`: with the weights 1, 1 the recurrence is theirs,
        c' = ℓ_1 c + (ℓ_0 - ℓ_1) h(0) + ∑_(k ≥ 2) ℓ_k h(k),
    with ℓ_k (`lagAt`) the Lagrange basis of the nodes 0, .., e + 1 at r, as a product of quotients.
    Sound if w(1) ≠ 0 and the nodes are distinct in the field.
 4. `Basis.cubic`, for degree 3, sends the values at 0 and -1 and the coefficient of X^3: the
    programs' SC3. `Basis.next_cubic_plain`: with the weights 1, 1, and if 2 ≠ 0, the recurrence is
    theirs,
        c' = c (r + r^2)/2 + h(0) (1 - r/2 - 3 r^2/2) + h(-1) (r^2 - r)/2 + h3 (r^3 - r).
    Sound if w(1) ≠ 0 and 2 ≠ 0.
All three are complete if w(1) ≠ 0 and the nodes 0, .., e + 1 are distinct in the field. Not here:
masks and affine forms (Blocks/SumCheckBlock.lean).

Notation (as in Alg/SumCheck.lean): `g : (ι → K) → K`: the summand, a function of the variables ι;
`d : ι → ℕ`: the degree bounds in `DegLE d g` (Alg/Poly.lean); `wt v`: the weights of the variable
v; `i`: the variable that the round binds; `rest`: the variables that are still unbound after it;
`z`: the point in which the earlier challenges are stored; `BadRound`: the challenge r of the round
that binds i is bad: the running claim c before the round is false, and the running claim after it
is true.
-/
import Alg.SumCheck
import Alg.RoundValues
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

set_option autoImplicit false

namespace Alg

open Finset Polynomial

/-! ## 1. The record and its two properties -/

/-- How the polynomial of a round of degree e + 1 is written in e + 1 scalars: data only. -/
structure Basis (K : Type) [Field K] (e : ℕ) where
  /-- the coefficient of the running claim in the next running claim, from the weights and the
  challenge -/
  cClaim : (Bool → K) → K → K
  /-- the coefficients of the scalars in the next running claim, from the weights and the
  challenge -/
  cMsg : (Bool → K) → K → Fin (e + 1) → K
  /-- the honest scalars, from the values of the true round polynomial -/
  scal : (K → K) → Fin (e + 1) → K

namespace Basis

variable {K : Type} [Field K] {e : ℕ}

/-- The verifier's recurrence: the next running claim, from the weights w, the running claim c, the
scalars m and the challenge r. -/
def next (b : Basis K e) (w : Bool → K) (c : K) (m : Fin (e + 1) → K) (r : K) : K :=
  b.cClaim w r * c + ∑ j, b.cMsg w r j * m j

/-- Whatever is sent, the next running claim is h(r) for one polynomial h of degree at most e + 1
with Λ(h) = c. -/
def Sound (b : Basis K e) (w : Bool → K) : Prop :=
  ∀ (c : K) (m : Fin (e + 1) → K),
    ∃ h : K[X], h.natDegree ≤ e + 1 ∧ lam w h = c ∧ ∀ r, b.next w c m r = h.eval r

/-- For every polynomial q of degree at most e + 1: from Λ(q) and the honest scalars of q, the next
running claim is q(r). -/
def Complete (b : Basis K e) (w : Bool → K) : Prop :=
  ∀ q : K[X], q.natDegree ≤ e + 1 → ∀ r, b.next w (lam w q) (b.scal fun t => q.eval t) r = q.eval r

/-- Over a finite field, under `hg`, `hD`, `hs` (sound if w(1) ≠ 0): at most e + 1 challenges of a
round are bad, whatever the prover sends. The condition w(1) ≠ 0 is part of the counted predicate,
as in `coeffNext_count_bad_le`. -/
theorem count_bad_le [Finite K] {ι : Type} [DecidableEq ι] {d : ι → ℕ} {g : (ι → K) → K}
    (hg : DegLE d g) (wt : ι → Bool → K) (i : ι) (rest : List ι) (z : ι → K) (hD : d i ≤ e + 1)
    (b : Basis K e) (hs : wt i true ≠ 0 → b.Sound (wt i)) (c : K) (m : Fin (e + 1) → K) :
    Nat.card {r : K // wt i true ≠ 0 ∧ BadRound wt g i rest z c (b.next (wt i) c m) r} ≤ e + 1 := by
  by_cases hw : wt i true = 0
  · rw [count_eq_zero fun r hr => hr.1 hw]
    exact Nat.zero_le _
  · exact le_trans (count_mono fun r hr => hr.2)
      (sumcheck_round_of_format hg wt i rest z hD c _ (hs hw c m))

/-- The honest round, under `hg`, `hD`, `hc` (complete): from the true running claim and the honest
scalars, which are computed from sums of the summand, the next running claim is true. -/
theorem next_roundPoly {ι : Type} [DecidableEq ι] {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g)
    (wt : ι → Bool → K) (i : ι) (rest : List ι) (z : ι → K) (hD : d i ≤ e + 1) (b : Basis K e)
    (hc : b.Complete (wt i)) (r : K) :
    b.next (wt i) (sumOutL wt (i :: rest) g z)
        (b.scal fun t => sumOutL wt rest g (Function.update z i t)) r =
      sumOutL wt rest g (Function.update z i r) := by
  have h := hc (roundPoly hg wt i rest z) ((natDegree_roundPoly_le hg wt i rest z).trans hD) r
  simp only [eval_roundPoly, lam_roundPoly] at h
  exact h

/-! ## 2. The value at 0 and the coefficients of X^2, .., X^(e+1) -/

variable (K e) in
/-- The value at 0 and the coefficients of X^2, .., X^(e+1). The honest coefficients are computed
from the values at 0, .., e + 1 (Alg/RoundValues.lean). -/
def coeff : Basis K e where
  cClaim w r := r / w true
  cMsg w r := Fin.cons (1 - r - r * w false / w true) fun j : Fin e => r ^ ((j : ℕ) + 2) - r
  scal v := valueScalars e fun k => v (k : K)

theorem next_coeff (w : Bool → K) (c : K) (m : Fin (e + 1) → K) (r : K) :
    (coeff K e).next w c m r = coeffNext w c m r := rfl

theorem sound_coeff {w : Bool → K} (hw : w true ≠ 0) : (coeff K e).Sound w :=
  (coeffFormat w hw e).sound

theorem complete_coeff (hnode : Function.Injective (node e : Fin (e + 2) → K))
    {w : Bool → K} (hw : w true ≠ 0) : (coeff K e).Complete w := by
  intro q hq r
  have h := (coeffFormat w hw e).complete q hq r
  show r / w true * lam w q + ∑ j, _ * valueScalars e (fun k : ℕ => q.eval (k : K)) j = _
  rw [valueScalars_eq hnode q hq]
  exact h

/-! ## 3. The values at 0, 2, 3, .., e + 1 -/

end Basis

variable {K : Type} [Field K]

/-- The Lagrange basis polynomial number k of the nodes 0, .., D, at r: the product of (r - m) / (k
- m) over the other nodes m. -/
def lagAt (D : ℕ) (k : Fin (D + 1)) (r : K) : K :=
  ∏ m ∈ univ.erase k, (r - ((m : ℕ) : K)) / (((k : ℕ) : K) - ((m : ℕ) : K))

theorem lagAt_eq_ell (e : ℕ) (k : Fin (e + 2)) (r : K) : lagAt (e + 1) k r = ell e k r := by
  unfold lagAt ell Lagrange.basis
  rw [eval_prod]
  refine prod_congr rfl fun m _ => ?_
  unfold Lagrange.basisDivisor node
  rw [eval_mul, eval_C, eval_sub, eval_X, eval_C, div_eq_mul_inv, mul_comm]

namespace Basis

variable {e : ℕ}

variable (K e) in
/-- The values at 0, 2, 3, .., e + 1; the value at 1 is eliminated by the round's equation. -/
def values : Basis K e where
  cClaim w r := lagAt (e + 1) 1 r / w true
  cMsg w r := Fin.cons (lagAt (e + 1) 0 r - lagAt (e + 1) 1 r * w false / w true)
    fun j : Fin e => lagAt (e + 1) j.succ.succ r
  scal v := Fin.cons (v 0) fun j : Fin e => v (((j : ℕ) + 2 : ℕ) : K)

theorem sound_values (hnode : Function.Injective (node e : Fin (e + 2) → K))
    {w : Bool → K} (hw : w true ≠ 0) : (values K e).Sound w := by
  intro c m
  obtain ⟨h, h1, h2, h3⟩ := (valueFormat w hw e hnode).sound c m
  refine ⟨h, h1, h2, fun r => ?_⟩
  rw [← h3 r]
  unfold next values
  simp only [lagAt_eq_ell]
  rfl

theorem complete_values (hnode : Function.Injective (node e : Fin (e + 2) → K))
    {w : Bool → K} (hw : w true ≠ 0) : (values K e).Complete w := by
  intro q hq r
  rw [← (valueFormat w hw e hnode).complete q hq r]
  unfold next values
  simp only [lagAt_eq_ell]
  rfl

/-- With the weights 1, 1 the recurrence is that of the programs' SCD: c' = ℓ_1 c + (ℓ_0 - ℓ_1)
h(0) + ∑_(k ≥ 2) ℓ_k h(k). -/
theorem next_values_plain (c : K) (m : Fin (e + 1) → K) (r : K) :
    (values K e).next (fun _ => 1) c m r =
      lagAt (e + 1) 1 r * c + (lagAt (e + 1) 0 r - lagAt (e + 1) 1 r) * m 0 +
        ∑ j : Fin e, lagAt (e + 1) j.succ.succ r * m j.succ := by
  unfold next values
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, div_one, mul_one]
  ring

/-! ## 4. Degree 3: the values at 0 and -1 and the coefficient of X^3 -/

variable (K) in
/-- Degree 3: the values at 0 and -1 and the coefficient of X^3. The honest coefficient is computed
from the values at 0, 1, 2, 3. -/
def cubic : Basis K 2 where
  cClaim w r := (r + r ^ 2) / 2 / w true
  cMsg w r := ![1 - r ^ 2 - (r + r ^ 2) / 2 * w false / w true, (r ^ 2 - r) / 2, r ^ 3 - r]
  scal v := ![v 0, v (-1), coeffOfValues 3 (fun k => v (k : K)) 3]

theorem next_cubic (w : Bool → K) (c : K) (m : Fin 3 → K) (r : K) :
    (cubic K).next w c m r =
      (r + r ^ 2) / 2 / w true * c + (1 - r ^ 2 - (r + r ^ 2) / 2 * w false / w true) * m 0 +
        (r ^ 2 - r) / 2 * m 1 + (r ^ 3 - r) * m 2 := by
  unfold next cubic
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- With the weights 1, 1, and if 2 ≠ 0, the recurrence is that of the programs' SC3. -/
theorem next_cubic_plain (h2 : (2 : K) ≠ 0) (c : K) (m : Fin 3 → K) (r : K) :
    (cubic K).next (fun _ => 1) c m r =
      c * ((r + r ^ 2) / 2) + m 0 * (1 - r / 2 - 3 * r ^ 2 / 2) +
        m 1 * ((r ^ 2 - r) / 2) + m 2 * (r ^ 3 - r) := by
  rw [next_cubic]
  simp only [div_one, mul_one]
  field_simp
  ring

theorem sound_cubic (h2 : (2 : K) ≠ 0) {w : Bool → K} (hw : w true ≠ 0) : (cubic K).Sound w := by
  intro c m
  refine ⟨C (m 2) * X ^ 3 + C (((c - w false * m 0) / w true + m 1) / 2 - m 0) * X ^ 2 +
      C (((c - w false * m 0) / w true - m 1) / 2 - m 2) * X + C (m 0),
    natDegree_cubic_le, ?_, fun r => ?_⟩
  · unfold lam
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    field_simp
    ring
  · rw [next_cubic]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    field_simp
    ring

/-- If the nodes 0, 1, 2, .. are distinct in the field, 2 is not 0. -/
theorem two_ne_zero_of_node (hnode : Function.Injective (node (e + 1) : Fin (e + 1 + 2) → K)) :
    (2 : K) ≠ 0 := by
  intro h
  have h1 : (node (e + 1) (⟨2, by omega⟩ : Fin (e + 1 + 2)) : K) = node (e + 1) ⟨0, by omega⟩ := by
    show ((2 : ℕ) : K) = ((0 : ℕ) : K)
    rw [Nat.cast_ofNat, Nat.cast_zero]
    exact h
  have h3 : (2 : ℕ) = 0 := congrArg Fin.val (hnode h1)
  omega

theorem complete_cubic (hnode : Function.Injective (node 2 : Fin (2 + 2) → K))
    {w : Bool → K} (hw : w true ≠ 0) : (cubic K).Complete w := by
  intro q hq r
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_node (e := 1) hnode
  have hc : coeffOfValues 3 (fun k : ℕ => q.eval (k : K)) 3 = q.coeff 3 :=
    (coeff_eq_coeffOfValues (D := 3) hnode q hq le_rfl).symm
  have hev : ∀ x : K,
      q.eval x = q.coeff 0 + q.coeff 1 * x + q.coeff 2 * x ^ 2 + q.coeff 3 * x ^ 3 := by
    intro x
    rw [eval_eq_sum_range' (show q.natDegree < 4 by omega)]
    simp only [sum_range_succ, range_zero, sum_empty]
    ring
  rw [next_cubic]
  show _ * lam w q + _ * q.eval 0 + _ * q.eval (-1) +
      _ * coeffOfValues 3 (fun k : ℕ => q.eval (k : K)) 3 = _
  rw [hc]
  unfold lam
  rw [hev 0, hev 1, hev (-1), hev r]
  field_simp
  ring

end Basis

end Alg
