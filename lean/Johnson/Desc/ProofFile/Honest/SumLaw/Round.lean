-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Round.lean: ONE ROUND OF THE MASKED SUMCHECK, THE HONEST PART's
TEXT AGAINST THE VERIFIER's: what `sumPart` (Honest/Sum.lean) sends for a variable with at least two
coefficients, whose share of the hiding polynomial has as many members (the tie to the part's moves:
Out.lean, Reads.lean), completed by the verifier's `complete` (Johnson/Desc/Part/MaskedSum4.lean) at
a running claim of the right form, is the round's true polynomial; so the next running claim has
that form again. Statements with their proofs. ρ: any reading. cn: any way of writing an element
anew that does not change its reading (a part's scalars are laid into words below the prime).

The form of a running claim, in front of the round of the variable v, whose share of the hiding
polynomial is w, with the later variables' shares in rest:
    a + B + tailSum ((v, w) :: rest) + eps * (the summand's claim).
a: the accumulator of the part's own walk (`hAt`). B: ANY element of the field. It stands for the
term that the part's text does not hold: what the claimed form is worth on the shown values less
what it is worth on the hidden ones, times eps and the psi of the variables passed. In a round it is
multiplied by psi, so it lies wholly in the coefficient that is not sent: what is sent does not
depend on it, and `complete` makes it up.
Main names:
  `leftOut v`: the number of the coefficient that is not sent. `cutOf v P`: a list without it.
  `sentOfL_eq`, `cutOf_length`, `complete_coeff`, `psi_coeff`, `mom_leftOut`: the pieces.
  `hAt_nil`, `hAt_cons`, `tailSum_cons`: the steps of the part's walk.
  `poly_round`: the part's polynomial of a round, read.
  `round_poly`: **what the verifier completes is B psi plus the part's polynomial.**
  `round_reads`: **the next running claim.**

Limits. One round. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Lists
import Johnson.Desc.Part.MaskedSumHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum
open OnBytes.Desc.First.P1 (Wt)
open Polynomial

/-- The number of the coefficient that is not sent. -/
def leftOut : Var → Nat
  | .plain _ => 1
  | .point _ _ => 0

/-- A list without the member of that number. -/
def cutOf : Var → List E → List E
  | .plain _, P => P.take 1 ++ P.drop 2
  | .point _ _, P => P.drop 1

theorem sentOfL_eq (v : Var) (g : List E) : sentOfL v g = cutOf v (padTo v.d g) := by
  cases v <;> rfl

theorem cutOf_length (v : Var) (P : List E) (hP : P.length = v.d) (h2 : 2 ≤ v.d) :
    (cutOf v P).length + 1 = v.d := by
  cases v with
  | plain d =>
    have h : 2 ≤ d := h2
    have hl : P.length = d := hP
    show (P.take 1 ++ P.drop 2).length + 1 = d
    rw [List.length_append, List.length_take, List.length_drop, hl]
    omega
  | point z d =>
    have h : 2 ≤ d := h2
    have hl : P.length = d := hP
    show (P.drop 1).length + 1 = d
    rw [List.length_drop, hl]
    omega

/-! ## The steps of the part's walk -/

theorem hAt_nil (v : Var) (w : List E) (rest : List (Var × List E)) (a : E) :
    hAt ((v, w) :: rest) [] a = addL (addL (scaleL a (psiL v)) w) [tailSum rest] := by
  rw [hAt.eq_def]

theorem hAt_cons (v : Var) (w : List E) (rest : List (Var × List E)) (r : E) (rs : List E) (a : E) :
    hAt ((v, w) :: rest) (r :: rs) a = hAt rest rs (addE (mulE a (psiAt v r)) (valueAt w r)) := by
  rw [hAt.eq_def]

theorem tailSum_cons (v : Var) (w : List E) (rest : List (Var × List E)) :
    tailSum ((v, w) :: rest) = addE (sumOf v w) (mulE (sumPow v 0) (tailSum rest)) := by
  rw [tailSum.eq_def]

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## What the verifier completes -/

/-- All coefficients but the one that is not sent are the list's. -/
theorem complete_coeff (cn : E → E) (hcn : ∀ x, ρ.val (cn x) = ρ.val x) (v : Var) (h2 : 2 ≤ v.d)
    (P : List E) (hP : P.length = v.d) (c : E) (i : Nat) (hi : i ≠ leftOut v) :
    (polyOf ρ (complete v ((cutOf v P).map cn) c)).coeff i = ρ.val (P.getD i zeroE) := by
  rw [polyOf_coeff]
  cases v with
  | plain d =>
    have h : 2 ≤ d := h2
    have hl : P.length = d := hP
    match P, hl with
    | [], hl => simp only [List.length_nil] at hl; omega
    | [_], hl => simp only [List.length_cons, List.length_nil] at hl; omega
    | p0 :: p1 :: high, _ =>
      have e : complete (.plain d) ((cutOf (.plain d) (p0 :: p1 :: high)).map cn) c =
          cn p0 :: subE c (addE (addE (cn p0) (cn p0)) (total (high.map cn))) :: high.map cn := rfl
      rw [e]
      match i, hi with
      | 0, _ => exact hcn p0
      | 1, hi => exact absurd rfl hi
      | i + 2, _ =>
        rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
          map_getD ρ cn hcn]
  | point z d =>
    have h : 2 ≤ d := h2
    have hl : P.length = d := hP
    match P, hl with
    | [], hl => simp only [List.length_nil] at hl; omega
    | p0 :: high, _ =>
      have e : complete (.point z d) ((cutOf (.point z d) (p0 :: high)).map cn) c =
          subE c (mulE z (total (high.map cn))) :: high.map cn := rfl
      rw [e]
      match i, hi with
      | 0, hi => exact absurd rfl hi
      | i + 1, _ => rw [List.getD_cons_succ, List.getD_cons_succ, map_getD ρ cn hcn]

/-- psi has the one coefficient that is not sent. -/
theorem psi_coeff (v : Var) (i : Nat) (hi : i ≠ leftOut v) : (v.wt ρ).psi.coeff i = 0 := by
  cases v with
  | plain d =>
    show (X : K[X]).coeff i = 0
    rw [coeff_X, if_neg (fun h => hi h.symm)]
  | point z d =>
    have hi' : i ≠ 0 := hi
    show (1 : K[X]).coeff i = 0
    rw [coeff_one, if_neg hi']

theorem mom_leftOut (v : Var) : (v.wt ρ).mom (leftOut v) = 1 := by
  cases v with
  | plain d =>
    show (if (1 : Nat) = 0 then (2 : K) else 1) = 1
    rw [if_neg Nat.one_ne_zero]
  | point z d =>
    show (if (0 : Nat) = 0 then (1 : K) else ρ.val z) = 1
    rw [if_pos rfl]

theorem leftOut_lt (v : Var) (h2 : 2 ≤ v.d) : leftOut v < (v.wt ρ).d := by
  rw [Var.wt_d]
  cases v with
  | plain d =>
    have h : 2 ≤ d := h2
    show 1 < d
    omega
  | point z d =>
    have h : 2 ≤ d := h2
    show 0 < d
    omega

/-! ## The round -/

/-- **The part's polynomial of a round, read.** -/
theorem poly_round (v : Var) (h2 : 2 ≤ v.d) (w : List E) (hw : w.length = v.d)
    (rest : List (Var × List E)) (a eps : E) (g : List E) :
    polyOf ρ (padTo v.d (addL (hAt ((v, w) :: rest) [] a) (scaleL eps g))) =
      C (ρ.val a) * (v.wt ρ).psi + polyOf ρ w + C (ρ.val (tailSum rest)) +
        C (ρ.val eps) * polyOf ρ (padTo v.d g) := by
  rw [hAt_nil, polyOf_padTo_addL, polyOf_padTo_scaleL, polyOf_padTo_addL, polyOf_padTo_addL,
    polyOf_padTo_scaleL, polyOf_padTo ρ v.d (psiL v) (Nat.le_trans (psiL_length v) h2),
    polyOf_padTo ρ v.d w (Nat.le_of_eq hw),
    polyOf_padTo ρ v.d [tailSum rest] (by show 1 ≤ v.d; omega), polyOf_psiL, polyOf_one]

/-- **What the verifier completes**, at a running claim of the form, is B psi plus the part's
polynomial of the round, cut or filled to the variable's number of coefficients. -/
theorem round_poly (cn : E → E) (hcn : ∀ x, ρ.val (cn x) = ρ.val x) (v : Var) (h2 : 2 ≤ v.d)
    (w : List E) (hw : w.length = v.d) (rest : List (Var × List E)) (a eps : E) (g : List E)
    (c : E) (B : K)
    (hc : ρ.val c = ρ.val a + B + ρ.val (tailSum ((v, w) :: rest)) +
      ρ.val eps * ρ.val (sumOf v (padTo v.d g))) :
    polyOf ρ (complete v
        ((sentOfL v (addL (hAt ((v, w) :: rest) [] a) (scaleL eps g))).map cn) c) =
      C B * (v.wt ρ).psi +
        polyOf ρ (padTo v.d (addL (hAt ((v, w) :: rest) [] a) (scaleL eps g))) := by
  obtain ⟨P, hP⟩ : ∃ P, P = padTo v.d (addL (hAt ((v, w) :: rest) [] a) (scaleL eps g)) := ⟨_, rfl⟩
  have hPl : P.length = v.d := by rw [hP, padTo_length]
  have hPp := poly_round ρ v h2 w hw rest a eps g
  rw [← hP] at hPp
  rw [sentOfL_eq, ← hP]
  refine poly_eq_of (v.wt ρ) (leftOut v) (leftOut_lt ρ v h2)
    (by rw [mom_leftOut]; exact one_ne_zero) _ _ ?_ ?_
  · rw [complete_sum ρ v _ c (by rw [List.length_map]; exact cutOf_length v P hPl h2) h2,
      Wt.sum_add, Wt.sum_C_mul, sum_psi ρ v h2, hPp, Wt.sum_add, Wt.sum_add, Wt.sum_add,
      Wt.sum_C_mul, Wt.sum_C_mul, sum_psi ρ v h2, sum_C ρ v (by omega), ← sumOf_val ρ v w hw,
      ← sumOf_val ρ v (padTo v.d g) (padTo_length _ _), hc, tailSum_cons, ρ.add, ρ.mul,
      sumPow_val]
    ring
  · intro i hi
    rw [complete_coeff ρ cn hcn v h2 P hPl c i hi, coeff_add, coeff_C_mul, psi_coeff ρ v i hi,
      mul_zero, zero_add, polyOf_coeff]

/-- **The next running claim.** -/
theorem round_reads (cn : E → E) (hcn : ∀ x, ρ.val (cn x) = ρ.val x) (v : Var) (h2 : 2 ≤ v.d)
    (w : List E) (hw : w.length = v.d) (rest : List (Var × List E)) (a eps : E) (g : List E)
    (c r : E) (B : K)
    (hc : ρ.val c = ρ.val a + B + ρ.val (tailSum ((v, w) :: rest)) +
      ρ.val eps * ρ.val (sumOf v (padTo v.d g))) :
    ρ.val (valueAt (complete v
        ((sentOfL v (addL (hAt ((v, w) :: rest) [] a) (scaleL eps g))).map cn) c) r) =
      ρ.val (addE (mulE a (psiAt v r)) (valueAt w r)) + B * ρ.val (psiAt v r) +
        ρ.val (tailSum rest) + ρ.val eps * ρ.val (valueAt (padTo v.d g) r) := by
  rw [← polyOf_eval, round_poly ρ cn hcn v h2 w hw rest a eps g c B hc,
    poly_round ρ v h2 w hw rest a eps g]
  simp only [eval_add, eval_mul, eval_C, psiAt_val, polyOf_eval, ρ.add, ρ.mul]
  ring

end ProofFile.Honest.SumLaw

end

#print axioms ProofFile.Honest.SumLaw.sentOfL_eq
#print axioms ProofFile.Honest.SumLaw.cutOf_length
#print axioms ProofFile.Honest.SumLaw.hAt_nil
#print axioms ProofFile.Honest.SumLaw.hAt_cons
#print axioms ProofFile.Honest.SumLaw.tailSum_cons
#print axioms ProofFile.Honest.SumLaw.complete_coeff
#print axioms ProofFile.Honest.SumLaw.psi_coeff
#print axioms ProofFile.Honest.SumLaw.mom_leftOut
#print axioms ProofFile.Honest.SumLaw.leftOut_lt
#print axioms ProofFile.Honest.SumLaw.poly_round
#print axioms ProofFile.Honest.SumLaw.round_poly
#print axioms ProofFile.Honest.SumLaw.round_reads
