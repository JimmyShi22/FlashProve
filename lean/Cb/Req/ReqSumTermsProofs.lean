-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSumTermsProofs.lean: the proofs of Cb/Req/ReqSumTerms.lean.

Main names (statements and hypotheses: Cb/Req/ReqSumTerms.lean):
  `tri_stepsOf`: `Steps.Tri` (Cb/Gen/SumSteps.lean) of `stepsOf nc as cs`.
  `out_stepsOf`: the summand at the atoms' values.
  `lt_maxAtom`, `le_maxLen`: a term's atoms below `maxAtom as`, no more than `maxLen as`.

Limits: what the head of Cb/Req/ReqSumTerms.lean lists as not said is not said here either.
-/
import Cb.Req.ReqSumTerms
import Cb.Gen.SumStepsProofs

set_option autoImplicit false

namespace Cb.Req
open Blocks

section
variable {E : Type} [CommRing E]

/-- For a list r that is not empty: if, under the values Y, each variable o + i holds the product of
its pair, the pair that is left multiplies to Y cur times the product of Y over r. -/
theorem mulUp_val (Y : ℕ → E) :
    ∀ (r : List ℕ) (o cur : ℕ), r ≠ [] →
      (∀ i, i < (mulUp o cur r).length →
        Y (o + i) = Y ((mulUp o cur r).getD i (0, 0)).1 * Y ((mulUp o cur r).getD i (0, 0)).2) →
      Y (lastPair o cur r).1 * Y (lastPair o cur r).2 = Y cur * (r.map Y).prod
  | [], _, _, h, _ => absurd rfl h
  | [a], o, cur, _, _ => by simp [lastPair]
  | a :: b :: r, o, cur, _, h => by
      have h0 : Y o = Y cur * Y a := h 0 (by simp [mulUp])
      have ih := mulUp_val Y (b :: r) (o + 1) o (by simp) fun i hi => by
        have h1 := h (i + 1) (by simpa [mulUp] using hi)
        have e : o + 1 + i = o + (i + 1) := by omega
        rw [e, h1]
        rfl
      show Y (lastPair (o + 1) o (b :: r)).1 * Y (lastPair (o + 1) o (b :: r)).2 = _
      rw [ih, h0]
      simp only [List.map_cons, List.prod_cons]
      ring

end

/-- If cur and the atoms of r are below o, a partial product names earlier variables only. -/
theorem mulUp_lt :
    ∀ (r : List ℕ) (o cur : ℕ), cur < o → (∀ j ∈ r, j < o) →
      ∀ i, i < (mulUp o cur r).length →
        ((mulUp o cur r).getD i (0, 0)).1 < o + i ∧ ((mulUp o cur r).getD i (0, 0)).2 < o + i
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | [_], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a :: b :: r, o, cur, hc, hr, 0, _ => ⟨hc, hr a (by simp)⟩
  | a :: b :: r, o, cur, _, hr, i + 1, hi => by
      have ih := mulUp_lt (b :: r) (o + 1) o (Nat.lt_succ_self o)
        (fun j hj => Nat.lt_succ_of_lt (hr j (List.mem_cons_of_mem a hj)))
        i (by simpa [mulUp] using hi)
      have e : o + 1 + i = o + (i + 1) := by omega
      rw [e] at ih
      exact ih

theorem lastPair_lt :
    ∀ (r : List ℕ) (o cur : ℕ), cur < o → (∀ j ∈ r, j < o) →
      (lastPair o cur r).1 < o + (mulUp o cur r).length ∧
      (lastPair o cur r).2 < o + (mulUp o cur r).length
  | [], _, _, hc, _ => ⟨hc, hc⟩
  | [a], _, _, hc, hr => ⟨hc, hr a (by simp)⟩
  | a :: b :: r, o, cur, _, hr => by
      have ih := lastPair_lt (b :: r) (o + 1) o (Nat.lt_succ_self o) fun j hj =>
        Nat.lt_succ_of_lt (hr j (List.mem_cons_of_mem a hj))
      have e : o + 1 + (mulUp (o + 1) o (b :: r)).length =
          o + (mulUp o cur (a :: b :: r)).length := by
        simp only [mulUp, List.length_cons]
        omega
      rw [e] at ih
      exact ih

theorem termAux_lt (as : List ℕ) (o : ℕ) (h : ∀ j ∈ as, j < o)
    (i : ℕ) (hi : i < (termAux o as).length) :
    ((termAux o as).getD i (0, 0)).1 < o + i ∧ ((termAux o as).getD i (0, 0)).2 < o + i := by
  cases as with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons a r =>
    exact mulUp_lt r o a (h a (by simp)) (fun j hj => h j (List.mem_cons_of_mem a hj)) i hi

theorem auxAll_lt :
    ∀ (ts : List (List ℕ)) (o : ℕ), (∀ l ∈ ts, ∀ j ∈ l, j < o) →
      ∀ i, i < (auxAll o ts).length →
        ((auxAll o ts).getD i (0, 0)).1 < o + i ∧ ((auxAll o ts).getD i (0, 0)).2 < o + i
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | as :: ts, o, h, i, hi => by
      by_cases h1 : i < (termAux o as).length
      · show ((termAux o as ++ _).getD i (0, 0)).1 < _ ∧ ((termAux o as ++ _).getD i (0, 0)).2 < _
        rw [List.getD_append _ _ _ _ h1]
        exact termAux_lt as o (h as (by simp)) i h1
      · have h2 : (termAux o as).length ≤ i := Nat.le_of_not_lt h1
        have hi' : i < (termAux o as).length + (auxAll (o + (termAux o as).length) ts).length := by
          simpa [auxAll] using hi
        have ih := auxAll_lt ts (o + (termAux o as).length)
          (fun l hl j hj =>
            Nat.lt_of_lt_of_le (h l (List.mem_cons_of_mem as hl) j hj) (Nat.le_add_right _ _))
          (i - (termAux o as).length) (by omega)
        show ((termAux o as ++ _).getD i (0, 0)).1 < _ ∧ ((termAux o as ++ _).getD i (0, 0)).2 < _
        rw [List.getD_append_right _ _ _ _ h2]
        have e : o + (termAux o as).length + (i - (termAux o as).length) = o + i := by omega
        rw [e] at ih
        exact ih

section
variable {E : Type} [CommRing E]

theorem termLast_below (o : ℕ) (c : E) (as : List ℕ) (h : ∀ j ∈ as, j < o) :
    (termLast o c as).Below (o + (termAux o as).length) := by
  match as, h with
  | [], _ => exact ⟨fun t ht => absurd ht List.not_mem_nil, fun t ht => absurd ht List.not_mem_nil⟩
  | [a], h =>
    refine ⟨fun t ht => ?_, fun t ht => absurd ht List.not_mem_nil⟩
    obtain rfl : t = (c, a) := by simpa [termLast] using ht
    exact Nat.lt_of_lt_of_le (h a (by simp)) (Nat.le_add_right _ _)
  | a :: b :: r, h =>
    refine ⟨fun t ht => absurd ht List.not_mem_nil, fun t ht => ?_⟩
    obtain rfl : t = (c, lastPair o a (b :: r)) := by simpa [termLast] using ht
    exact lastPair_lt (b :: r) o a (h a (by simp)) fun j hj => h j (List.mem_cons_of_mem a hj)

omit [CommRing E] in
theorem below_mono {q : QStep E} {n m : ℕ} (h : q.Below n) (hnm : n ≤ m) : q.Below m :=
  ⟨fun t ht => Nat.lt_of_lt_of_le (h.1 t ht) hnm,
    fun t ht => ⟨Nat.lt_of_lt_of_le (h.2 t ht).1 hnm, Nat.lt_of_lt_of_le (h.2 t ht).2 hnm⟩⟩

theorem lastStep_below (cs : ℕ → E) :
    ∀ (ts : List (List ℕ)) (o k : ℕ),
      (∀ l ∈ ts, ∀ j ∈ l, j < o) → (lastStep cs o k ts).Below (o + (auxAll o ts).length)
  | [], _, _, _ => ⟨fun t ht => absurd ht List.not_mem_nil, fun t ht => absurd ht List.not_mem_nil⟩
  | as :: ts, o, k, h => by
      have h1 := below_mono (termLast_below o (cs k) as (h as (by simp)))
        (m := o + (auxAll o (as :: ts)).length) (by simp only [auxAll, List.length_append]; omega)
      have h2 := below_mono
        (lastStep_below cs ts (o + (termAux o as).length) (k + 1) fun l hl j hj =>
          Nat.lt_of_lt_of_le (h l (List.mem_cons_of_mem as hl) j hj) (Nat.le_add_right _ _))
        (m := o + (auxAll o (as :: ts)).length) (by simp only [auxAll, List.length_append]; omega)
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rcases List.mem_append.1 (show t ∈ (termLast o (cs k) as).lin ++ _ from ht) with ht | ht
        · exact h1.1 t ht
        · exact h2.1 t ht
      · rcases List.mem_append.1 (show t ∈ (termLast o (cs k) as).quad ++ _ from ht) with ht | ht
        · exact h1.2 t ht
        · exact h2.2 t ht

theorem termLast_eval (Y : ℕ → E) (o : ℕ) (c : E) (as : List ℕ)
    (h : ∀ i, i < (termAux o as).length →
      Y (o + i) = Y ((termAux o as).getD i (0, 0)).1 * Y ((termAux o as).getD i (0, 0)).2) :
    (termLast o c as).eval Y = c * (as.map Y).prod := by
  match as, h with
  | [], _ => simp [termLast, QStep.eval, linSum, termSum]
  | [a], _ => simp [termLast, QStep.eval, linSum, termSum]
  | a :: b :: r, h =>
    have h1 := mulUp_val Y (b :: r) o a (by simp) h
    simp only [termLast, QStep.eval, linSum, termSum, List.map_nil, List.sum_nil, List.map_cons,
      List.sum_cons, add_zero, zero_add]
    rw [mul_assoc, h1]
    simp only [List.map_cons, List.prod_cons]

theorem lastStep_eval (Y : ℕ → E) (cs : ℕ → E) :
    ∀ (ts : List (List ℕ)) (o k : ℕ),
      (∀ i, i < (auxAll o ts).length →
        Y (o + i) = Y ((auxAll o ts).getD i (0, 0)).1 * Y ((auxAll o ts).getD i (0, 0)).2) →
      (lastStep cs o k ts).eval Y =
        ((List.range ts.length).map fun m => cs (k + m) * ((ts.getD m []).map Y).prod).sum
  | [], _, _, _ => by simp [lastStep, QStep.eval, linSum, termSum]
  | as :: ts, o, k, h => by
      have h1 := termLast_eval Y o (cs k) as fun i hi => by
        have := h i (by simp only [auxAll, List.length_append]; omega)
        rw [show auxAll o (as :: ts) = termAux o as ++ auxAll (o + (termAux o as).length) ts
              from rfl,
          List.getD_append _ _ _ _ hi] at this
        exact this
      have h2 := lastStep_eval Y cs ts (o + (termAux o as).length) (k + 1) fun i hi => by
        have := h ((termAux o as).length + i) (by simp only [auxAll, List.length_append]; omega)
        rw [show auxAll o (as :: ts) = termAux o as ++ auxAll (o + (termAux o as).length) ts
              from rfl,
          List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left, ← Nat.add_assoc] at this
        exact this
      have e : (lastStep cs o k (as :: ts)).eval Y =
          (termLast o (cs k) as).eval Y +
            (lastStep cs (o + (termAux o as).length) (k + 1) ts).eval Y := by
        simp only [lastStep, QStep.eval, linSum, termSum, List.map_append, List.sum_append]
        ring
      rw [e, h1, h2, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.sum_cons, List.map_map]
      congr 1
      refine congrArg List.sum (List.map_congr_left fun m _ => ?_)
      show cs (k + 1 + m) * _ = cs (k + (m + 1)) * _
      rw [show k + 1 + m = k + (m + 1) by omega]
      rfl

end

theorem tri_stepsOf : Spec.tri_stepsOf := by
  intro E _ nc as cs h l hl
  by_cases h1 : l < (auxAll nc as).length
  · have h2 := auxAll_lt as nc h l h1
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈
          (if l < (auxAll nc as).length then
              (⟨0, [], [(1, (auxAll nc as).getD l (0, 0))]⟩ : QStep E)
            else lastStep cs nc 0 as).lin := ht
      rw [if_pos h1] at ht'
      exact absurd ht' List.not_mem_nil
    · have ht' : t ∈
          (if l < (auxAll nc as).length then
              (⟨0, [], [(1, (auxAll nc as).getD l (0, 0))]⟩ : QStep E)
            else lastStep cs nc 0 as).quad := ht
      rw [if_pos h1] at ht'
      obtain rfl : t = (1, (auxAll nc as).getD l (0, 0)) := by simpa using ht'
      exact h2
  · have hl' : l = (auxAll nc as).length := Nat.le_antisymm hl (Nat.le_of_not_lt h1)
    show (if l < (auxAll nc as).length then (⟨0, [], [(1, (auxAll nc as).getD l (0, 0))]⟩ : QStep E)
      else lastStep cs nc 0 as).Below (nc + l)
    rw [if_neg h1, hl']
    exact lastStep_below cs as nc 0 h

theorem out_stepsOf : Spec.out_stepsOf := by
  intro E _ nc as cs Y h
  obtain ⟨⟨hA, hO⟩, hY⟩ := hold_vals E (stepsOf nc as cs) Y (tri_stepsOf E nc as cs h)
  have hO' : (stepsOf nc as cs).out Y = (lastStep cs nc 0 as).eval ((stepsOf nc as cs).vals Y) := by
    rw [hO]
    show (if (auxAll nc as).length < (auxAll nc as).length then
          (⟨0, [], [(1, (auxAll nc as).getD (auxAll nc as).length (0, 0))]⟩ : QStep E)
        else lastStep cs nc 0 as).eval _ = _
    rw [if_neg (Nat.lt_irrefl _)]
  rw [hO', lastStep_eval _ cs as nc 0 fun i hi => by
    refine (hA i hi).trans ?_
    show (if i < (auxAll nc as).length then (⟨0, [], [(1, (auxAll nc as).getD i (0, 0))]⟩ : QStep E)
        else lastStep cs nc 0 as).eval _ = _
    rw [if_pos hi]
    simp [QStep.eval, linSum, termSum]]
  refine congrArg List.sum (List.map_congr_left fun m hm => ?_)
  have hm' : m < as.length := List.mem_range.1 hm
  rw [Nat.zero_add,
    List.map_congr_left fun j hj =>
      hY j
        (h (as.getD m []) (by rw [List.getD_eq_getElem _ _ hm']; exact List.getElem_mem hm') j hj)]

theorem lt_maxAtom : Spec.lt_maxAtom := by
  intro as
  induction as with
  | nil => intro l hl; exact absurd hl List.not_mem_nil
  | cons a ts ih =>
    have hin : ∀ (l : List ℕ), ∀ j ∈ l, j < (l.map (· + 1)).foldr max 0 := by
      intro l
      induction l with
      | nil => intro j hj; exact absurd hj List.not_mem_nil
      | cons x r ihr =>
        intro j hj
        simp only [List.map_cons, List.foldr_cons]
        rcases List.mem_cons.1 hj with rfl | hj
        · omega
        · have := ihr j hj
          omega
    intro l hl j hj
    simp only [maxAtom, List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hl with rfl | hl
    · have := hin l j hj
      omega
    · have := ih l hl j hj
      unfold maxAtom at this
      omega

theorem le_maxLen : Spec.le_maxLen := by
  intro as
  induction as with
  | nil => intro l hl; exact absurd hl List.not_mem_nil
  | cons a ts ih =>
    intro l hl
    simp only [maxLen, List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hl with rfl | hl
    · omega
    · have := ih l hl
      unfold maxLen at this
      omega

end Cb.Req
