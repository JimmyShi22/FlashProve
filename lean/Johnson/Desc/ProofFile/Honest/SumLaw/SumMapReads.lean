-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/SumMapReads.lean: WHAT THE MASKED SUMCHECK's PART SAYS OF ITS
POLYNOMIAL H, READ: where every variable has at least two coefficients it is what SumMap.lean of
this folder defines over a field. Definitions that the statements need, and statements with their
proofs.
Main names:
  `toK`: a variable with its point read.
  `sentOfL_read`: what is sent of a list, read.
  `sumOf_read`, `tail_read`: the part's sums, read: `tailSum` is `tailK`.
  `psiL_read`, `hAt_read`, `round_read`: one round's message, read: H's share as
    `sentK` has it, plus eps times the summand's list, coefficient by coefficient.

Limits. Every variable has at least two coefficients: a premise. No distribution occurs. No property
of a protocol is stated.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumMap
import Johnson.Desc.ProofFile.Honest.SumLaw.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum

variable {K : Type} [Field K] (ρ : Reading K)

/-- A variable with its point read. -/
def toK : Var → VK K
  | .plain d => (none, d)
  | .point z d => (some (ρ.val z), d)

/-- It keeps the number of coefficients. -/
theorem toK_snd (v : Var) : (toK ρ v).2 = v.d := by cases v <;> rfl

/-- A list, read, as a list by number. -/
theorem map_read (P : List E) :
    P.map ρ.val = (List.range P.length).map fun t => ρ.val (P.getD t zeroE) := by
  refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_range]) ?_
  intro i h1 _
  rw [List.length_map] at h1
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1]
  rfl

/-- **What is sent of a list, read.** -/
theorem sentOfL_read (v : Var) (h2 : 2 ≤ v.d) (g : List E) :
    (sentOfL v g).map ρ.val = cutK (toK ρ v) fun t => ρ.val (g.getD t zeroE) := by
  cases v with
  | plain d =>
    have hd : 2 ≤ d := h2
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    have hl := padTo_length (e + 2) g
    have hg : ∀ t, t < e + 2 → (padTo (e + 2) g).getD t zeroE = g.getD t zeroE := fun t ht => by
      rw [padTo_getD, if_pos ht]
    show ((padTo (e + 2) g).take 1 ++ (padTo (e + 2) g).drop 2).map ρ.val =
      ρ.val (g.getD 0 zeroE) ::
        ((List.range e).map (· + 2)).map fun t => ρ.val (g.getD t zeroE)
    rw [List.map_map]
    match hP : padTo (e + 2) g, hl with
    | p0 :: p1 :: rest, hl =>
      have hr : rest.length = e := by
        simp only [List.length_cons] at hl
        omega
      show ρ.val p0 :: rest.map ρ.val = _
      rw [map_read ρ rest, hr]
      have e0 : p0 = g.getD 0 zeroE := by
        rw [← hg 0 (by omega), hP]
        rfl
      rw [e0]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      show ρ.val (rest.getD t zeroE) = ρ.val (g.getD (t + 2) zeroE)
      rw [← hg (t + 2) (by have := List.mem_range.1 ht; omega), hP]
      rfl
    | [], hl => simp only [List.length_nil] at hl; omega
    | [_], hl => simp only [List.length_cons, List.length_nil] at hl; omega
  | point z d =>
    have hd : 2 ≤ d := h2
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hl := padTo_length (e + 1) g
    have hg : ∀ t, t < e + 1 → (padTo (e + 1) g).getD t zeroE = g.getD t zeroE := fun t ht => by
      rw [padTo_getD, if_pos ht]
    show ((padTo (e + 1) g).drop 1).map ρ.val =
      ((List.range e).map (· + 1)).map fun t => ρ.val (g.getD t zeroE)
    rw [List.map_map]
    match hP : padTo (e + 1) g, hl with
    | p0 :: rest, hl =>
      have hr : rest.length = e := by
        simp only [List.length_cons] at hl
        omega
      show rest.map ρ.val = _
      rw [map_read ρ rest, hr]
      refine List.map_congr_left fun t ht => ?_
      show ρ.val (rest.getD t zeroE) = ρ.val (g.getD (t + 1) zeroE)
      rw [← hg (t + 1) (by have := List.mem_range.1 ht; omega), hP]
      rfl
    | [], hl => simp only [List.length_nil] at hl; omega

/-- The part's way of summing, read, term by term. -/
theorem sumOf_read (v : Var) (g : List E) :
    ρ.val (sumOf v g) =
      ∑ t ∈ Finset.range g.length, (v.wt ρ).mom t * ρ.val (g.getD t zeroE) := by
  unfold sumOf
  rw [total_val, sumTerms_val ρ v g 0]
  exact Finset.sum_congr rfl fun t _ => by rw [Nat.zero_add]

/-- A share without a constant term, summed. f: the coins' readings by number, from i on. -/
theorem sum_inner (v : Var) (U : List E) (f : Nat → K) (i : Nat)
    (h : ∀ j, j < v.d - 1 → ρ.val (U.getD j zeroE) = f (i + j)) :
    ρ.val (sumOf v (zeroE :: padTo (v.d - 1) U)) = (v.wt ρ).mom 1 * rowSum f i (v.d - 1) := by
  rw [sumOf_read, List.length_cons, padTo_length, Finset.sum_range_succ']
  have e0 : ρ.val ((zeroE :: padTo (v.d - 1) U).getD 0 zeroE) = 0 := ρ.zero
  rw [e0, mul_zero, add_zero]
  unfold rowSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [List.getD_cons_succ, padTo_getD, if_pos ht', h t ht']
  congr 1
  cases v <;> rfl

/-- The last variable's share, summed. -/
theorem sum_last (v : Var) (h1 : 1 ≤ v.d) (U : List E) (f : Nat → K) (i : Nat)
    (h : ∀ j, j < v.d → ρ.val (U.getD j zeroE) = f (i + j)) :
    ρ.val (sumOf v (padTo v.d U)) =
      (v.wt ρ).mom 0 * f i + (v.wt ρ).mom 1 * rowSum f (i + 1) (v.d - 1) := by
  obtain ⟨e, he⟩ : ∃ e, v.d = e + 1 := ⟨v.d - 1, by omega⟩
  rw [sumOf_read, padTo_length, he, Finset.sum_range_succ', add_comm]
  congr 1
  · rw [padTo_getD, if_pos (by omega), h 0 (by omega)]
    rfl
  · show _ = _ * rowSum f (i + 1) e
    unfold rowSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    rw [padTo_getD, if_pos (by omega), h (t + 1) (by omega)]
    congr 1
    · cases v <;> rfl
    · congr 1
      omega

/-- **The part's sum of H over a list of variables, read.** f: the coins'
readings by number, from i on. -/
theorem tail_read : ∀ (vs : List Var) (U : List E) (f : Nat → K) (i : Nat),
    (∀ v ∈ vs, 2 ≤ v.d) →
    (∀ j, j < slots (vs.map (toK ρ)) → ρ.val (U.getD j zeroE) = f (i + j)) →
    ρ.val (tailSum (vs.zip (wOf vs U))) = tailK (vs.map (toK ρ)) f i
  | [], _, _, _, _, _ => ρ.zero
  | [v], U, f, i, h2, h => by
    have hd : 2 ≤ v.d := h2 v List.mem_cons_self
    have hs : slots ([v].map (toK ρ)) = v.d := by
      simp only [slots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, toK_snd]
      omega
    show ρ.val (addE (sumOf v (padTo v.d U)) (mulE (sumPow v 0) zeroE)) = _
    rw [ρ.add, ρ.mul, ρ.zero, mul_zero, add_zero,
      sum_last ρ v (by omega) U f i fun j hj => h j (by rw [hs]; exact hj)]
    cases v with
    | plain d =>
      show (2 : K) * f i + 1 * rowSum f (i + 1) (d - 1) = 2 * f i + rowSum f (i + 1) (d - 1)
      rw [one_mul]
    | point z d =>
      show (1 : K) * f i + ρ.val z * rowSum f (i + 1) (d - 1) =
        f i + ρ.val z * rowSum f (i + 1) (d - 1)
      rw [one_mul]
  | v :: v' :: vs, U, f, i, h2, h => by
    have hd : 2 ≤ v.d := h2 v List.mem_cons_self
    have hs : slots ((v :: v' :: vs).map (toK ρ)) =
        (v.d - 1) + slots ((v' :: vs).map (toK ρ)) := by
      simp only [slots, List.map_cons, List.sum_cons, toK_snd]
      omega
    have ih := tail_read (v' :: vs) (U.drop (v.d - 1)) f (i + (v.d - 1))
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) fun j hj => by
        rw [getD_drop, h (v.d - 1 + j) (by rw [hs]; omega)]
        congr 1
        omega
    show ρ.val (addE (sumOf v (zeroE :: padTo (v.d - 1) U))
      (mulE (sumPow v 0) (tailSum ((v' :: vs).zip (wOf (v' :: vs) (U.drop (v.d - 1))))))) = _
    rw [ρ.add, ρ.mul, ih, sumPow_val,
      sum_inner ρ v U f i fun j hj => h j (by rw [hs]; omega)]
    cases v with
    | plain d =>
      show (1 : K) * rowSum f i (d - 1) + 2 * _ = rowSum f i (d - 1) + 2 * _
      rw [one_mul]
      rfl
    | point z d =>
      show ρ.val z * rowSum f i (d - 1) + 1 * _ = ρ.val z * rowSum f i (d - 1) + _
      rw [one_mul]
      rfl

/-! ## A round's message -/

/-- psi has no coefficient but the one that is left out. -/
theorem psiL_read (v : Var) (t : Nat) (ht : t ≠ (if (toK ρ v).1.isSome then 0 else 1)) :
    ρ.val ((psiL v).getD t zeroE) = 0 := by
  cases v with
  | plain d =>
    have h1 : t ≠ 1 := ht
    match t with
    | 0 => exact ρ.zero
    | 1 => exact absurd rfl h1
    | _ + 2 => exact ρ.zero
  | point z d =>
    have h0 : t ≠ 0 := ht
    match t with
    | 0 => exact absurd rfl h0
    | _ + 1 => exact ρ.zero

/-- **H's round polynomial, read, at a coefficient that is sent.** f: the coins'
readings by number, from i on. a: what the variables passed have come to: it stands in the
coefficient that is left out alone. -/
theorem hAt_read (v : Var) (vs : List Var) (U : List E) (f : Nat → K) (i : Nat) (a : E)
    (h2 : ∀ x ∈ v :: vs, 2 ≤ x.d)
    (h : ∀ j, j < slots ((v :: vs).map (toK ρ)) → ρ.val (U.getD j zeroE) = f (i + j)) (t : Nat)
    (ht : t ∈ sentIdx (toK ρ v)) :
    ρ.val ((hAt ((v :: vs).zip (wOf (v :: vs) U)) [] a).getD t zeroE) =
      hK (toK ρ v) (vs.map (toK ρ)) f i t := by
  have hd : 2 ≤ v.d := h2 v List.mem_cons_self
  obtain ⟨ht1, ht2⟩ := mem_sentIdx (toK ρ v) (by rw [toK_snd]; exact hd) t ht
  rw [toK_snd] at ht1
  cases vs with
  | nil =>
    have hs : slots ([v].map (toK ρ)) = v.d := by
      simp only [slots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, toK_snd]
      omega
    show ρ.val ((addL (addL (scaleL a (psiL v)) (padTo v.d U)) [zeroE]).getD t zeroE) = f (i + t)
    rw [addL_getD, addL_getD, scaleL_getD, psiL_read ρ v t ht2, mul_zero, zero_add, padTo_getD,
      if_pos ht1, h t (by rw [hs]; exact ht1)]
    have e0 : ρ.val (([zeroE] : List E).getD t zeroE) = 0 := by
      cases t <;> exact ρ.zero
    rw [e0, add_zero]
  | cons v' vs =>
    have hs : slots ((v :: v' :: vs).map (toK ρ)) =
        (v.d - 1) + slots ((v' :: vs).map (toK ρ)) := by
      simp only [slots, List.map_cons, List.sum_cons, toK_snd]
      omega
    have hT := tail_read ρ (v' :: vs) (U.drop (v.d - 1)) f (i + (v.d - 1))
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) fun j hj => by
        rw [getD_drop, h (v.d - 1 + j) (by rw [hs]; omega)]
        congr 1
        omega
    show ρ.val ((addL (addL (scaleL a (psiL v)) (zeroE :: padTo (v.d - 1) U))
      [tailSum ((v' :: vs).zip (wOf (v' :: vs) (U.drop (v.d - 1))))]).getD t zeroE) =
      if t = 0 then tailK ((v' :: vs).map (toK ρ)) f (i + ((toK ρ v).2 - 1)) else f (i + t - 1)
    rw [addL_getD, addL_getD, scaleL_getD, psiL_read ρ v t ht2, mul_zero, zero_add, toK_snd]
    cases t with
    | zero =>
      rw [if_pos rfl]
      show ρ.val zeroE + ρ.val (tailSum _) = _
      rw [ρ.zero, zero_add, hT]
    | succ s =>
      rw [if_neg (Nat.succ_ne_zero s), List.getD_cons_succ, List.getD_cons_succ, padTo_getD,
        if_pos (by omega), h s (by rw [hs]; omega)]
      have e0 : ρ.val (([] : List E).getD s zeroE) = 0 := ρ.zero
      rw [e0, add_zero]
      rfl

/-- **One round's message, read.** -/
theorem round_read (v : Var) (vs : List Var) (U : List E) (f : Nat → K) (i : Nat) (a eps : E)
    (P : List E) (h2 : ∀ x ∈ v :: vs, 2 ≤ x.d)
    (h : ∀ j, j < slots ((v :: vs).map (toK ρ)) → ρ.val (U.getD j zeroE) = f (i + j)) :
    (sentOfL v (addL (hAt ((v :: vs).zip (wOf (v :: vs) U)) [] a) (scaleL eps P))).map ρ.val =
      cutK (toK ρ v) fun t =>
        hK (toK ρ v) (vs.map (toK ρ)) f i t + ρ.val eps * ρ.val (P.getD t zeroE) := by
  rw [sentOfL_read ρ v (h2 v List.mem_cons_self)]
  refine List.map_congr_left fun t ht => ?_
  rw [addL_getD, scaleL_getD, hAt_read ρ v vs U f i a h2 h t ht]

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.toK_snd
#print axioms ProofFile.Honest.SumLaw.map_read
#print axioms ProofFile.Honest.SumLaw.sentOfL_read
#print axioms ProofFile.Honest.SumLaw.sumOf_read
#print axioms ProofFile.Honest.SumLaw.sum_inner
#print axioms ProofFile.Honest.SumLaw.sum_last
#print axioms ProofFile.Honest.SumLaw.tail_read
#print axioms ProofFile.Honest.SumLaw.psiL_read
#print axioms ProofFile.Honest.SumLaw.hAt_read
#print axioms ProofFile.Honest.SumLaw.round_read
