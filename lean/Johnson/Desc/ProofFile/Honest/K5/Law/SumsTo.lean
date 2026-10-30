-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SumsTo.lean: a tame summand pays what the law of the masked
sumcheck's honest part leaves to its caller. Statements with their proofs, and one definition that a
proof needs. rho: any reading in a field (OnBytes/Model/HideLaws.lean).

What is owed. The law (Honest/SumLaw/Statement.lean, More.lean) asks of a caller `SumsTo`
(Honest/SumLaw/Terms.lean): round by round, the sum of the summand's polynomial, cut or filled to
the variable's number of coefficients, is the claim so far; the next claim is that polynomial's
value at the round's challenge. Here this is shown of a job that `jobOf` (Honest/K5/Job.lean) makes
of a summand in the form of Johnson/Desc/K5/Honest/Terms.lean.

THE MAIN STATEMENT IS CONDITIONAL: on `Summand.Tame` (Johnson/Desc/K5/Honest/Law/TermsLaw.lean),
which whoever lays the summand pays; on a call whose variables are all summed plainly and which has
ends.
Main names:
  `jobPoly_jobOf`, `withPoints_nil`, `callAt_jobOf`   a job made by `jobOf`: its polynomials are the
        summand's; it has no points, so the call in a run is the shape
  `polyOf_padTo_cut`, `value_padTo_cut`   a list whose members beyond d read 0, cut or filled to d,
        reads as the same polynomial
  `sumOf_plain`, `sumOf_point0`   the part's way of summing, at a list of the variable's length: the
        values at 0 and 1 added; at the point 0 the value at 0
  `valY`            the partial sums, and behind Y's challenge the polynomial in Y at it
  `sumsTo_summand`  **the statement, of a summand alone**
  `sumsTo_of_tame`  **the statement, of the job**: from the summand's total to the polynomial in Y
        at beta
  `last_is_formula`  that last value is the summand's formula on each end value plus beta times its
        mask entry
  `sumsTo_of_tame_at`, `last_is_formula_at`   the two at the challenges as one list, Y's last
Small facts on lists stand under `Lists`, here and in TermsLaw.lean; this file opens both.

Limits. One list of challenges at a time. No summand of the protocol is shown to be tame here. No
sumcheck is proved anew: the law is Honest/SumLaw's. Nothing is claimed on soundness, completeness
or hiding.
-/
import Johnson.Desc.K5.Honest.Law.TermsLaw
import Johnson.Desc.ProofFile.Honest.K5.Job
import Johnson.Desc.ProofFile.Honest.SumLaw.More

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call valueAt polyOf polyOf_coeff
  polyOf_natDegree_lt)
open OnBytes.Desc.First.P1 (Wt)
open ProofFile.Honest.SumLaw (SumsTo jobPoly sumsTo_of_vals padTo_getD padTo_length sumOf_val)
open H2K5.Honest (Summand read_valueAt)
open H2K5.Honest.Lists (getD_at)
open Polynomial

variable {W X : Type}

/-! ## 1 A job made of a summand -/

/-- Its polynomials are the summand's. -/
theorem jobPoly_jobOf (k : Call) (lead : W → Front X → List E) (S : W → Front X → Summand) (w : W)
    (fr : Front X) (m rs : List E) : jobPoly (jobOf k lead S) w fr m rs =
      if rs.length < k.vs.length then (S w fr).round rs else (S w fr).inY rs m := rfl

/-- Where no point is laid in, the variables stay. -/
theorem withPoints_nil : ∀ vs : List Var, withPoints vs [] = vs
  | [] => rfl
  | .plain d :: vs => by
    show Var.plain d :: withPoints vs [] = _
    rw [withPoints_nil vs]
  | .point z d :: vs => by
    show Var.point z d :: withPoints vs [] = _
    rw [withPoints_nil vs]

/-- The call in a run is the shape. -/
theorem callAt_jobOf (k : Call) (lead : W → Front X → List E) (S : W → Front X → Summand) (w : W)
    (fr : Front X) : (jobOf k lead S).callAt w fr = k := by
  show ({ k with vs := withPoints k.vs [] } : Call) = k
  rw [withPoints_nil]

/-! ## 2 Cutting, and the two ways of summing -/

variable {K : Type} [Field K] (ρ : Reading K)

/-- A list whose members beyond d read 0, cut or filled to d, is the same polynomial. -/
theorem polyOf_padTo_cut (d : Nat) (g : List E) (h : ∀ j, d ≤ j → ρ.val (g.getD j zeroE) = 0) :
    polyOf ρ (padTo d g) = polyOf ρ g := by
  ext i
  rw [polyOf_coeff, polyOf_coeff, padTo_getD]
  by_cases hi : i < d
  · rw [if_pos hi]
  · rw [if_neg hi, ρ.zero, h i (by omega)]

theorem value_padTo_cut (d : Nat) (g : List E) (h : ∀ j, d ≤ j → ρ.val (g.getD j zeroE) = 0)
    (x : E) : ρ.val (valueAt (padTo d g) x) = ρ.val (valueAt g x) := by
  rw [read_valueAt, read_valueAt, polyOf_padTo_cut ρ d g h]

/-- Summed plainly, a list of the variable's length gives its values at 0 and at 1, added. -/
theorem sumOf_plain (d : Nat) (g : List E) (h : g.length = d) :
    ρ.val (sumOf (.plain d) g) = ρ.val (valueAt g zeroE) + ρ.val (valueAt g oneE) := by
  rw [sumOf_val ρ (.plain d) g h, read_valueAt, read_valueAt, ρ.zero, ρ.one, Wt.sum]
  show ∑ i ∈ Finset.range d, (if i = 0 then (2 : K) else 1) * (polyOf ρ g).coeff i = _
  cases d with
  | zero =>
    rw [List.length_eq_zero_iff.1 h]
    simp [polyOf]
  | succ d =>
    have hdeg : (polyOf ρ g).natDegree < d + 1 := by
      have := polyOf_natDegree_lt ρ g (by omega)
      omega
    rw [eval_eq_sum_range' hdeg 1, ← coeff_zero_eq_eval_zero, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, one_pow, mul_one,
      one_mul]
    ring

/-- Summed at the point 0, it gives its value at 0. -/
theorem sumOf_point0 (d : Nat) (g : List E) (h : g.length = d) :
    ρ.val (sumOf (.point zeroE d) g) = ρ.val (valueAt g zeroE) := by
  rw [sumOf_val ρ (.point zeroE d) g h, read_valueAt, ρ.zero, Wt.sum]
  show ∑ i ∈ Finset.range d, (if i = 0 then (1 : K) else ρ.val zeroE) * (polyOf ρ g).coeff i = _
  cases d with
  | zero =>
    rw [List.length_eq_zero_iff.1 h]
    simp [polyOf]
  | succ d =>
    rw [← coeff_zero_eq_eval_zero, Finset.sum_range_succ', ρ.zero]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, zero_mul, one_mul,
      Finset.sum_const_zero, zero_add]

/-! ## 3 Lists by index -/

namespace Lists

theorem getD_map_append_lt {α β : Type} (f : α → β) (d : α) (p : β) : ∀ (l : List α) (i : Nat),
    i < l.length → (l.map f ++ [p]).getD i (f d) = f (l.getD i d)
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, 0, _ => rfl
  | x :: l, i + 1, h => by
    simp only [List.map_cons, List.cons_append, List.getD_cons_succ]
    exact getD_map_append_lt f d p l i (by simpa using h)

theorem take_succ_getD {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i < l.length →
    l.take (i + 1) = l.take i ++ [l.getD i d]
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, 0, _ => rfl
  | x :: l, i + 1, h => by
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    rw [take_succ_getD d l i (by simpa using h)]

end Lists

open Lists

/-! ## 4 The statement -/

/-- The partial sums behind the challenges passed; behind Y's challenge: the polynomial in Y, cut or
filled, at that challenge. -/
def valY (S : Summand) (dY : Nat) (m past : List E) : K :=
  if past.length ≤ S.vars then S.val ρ past
  else ρ.val (valueAt (padTo (dY + 1) (S.inY (past.take S.vars) m)) (past.getD S.vars zeroE))

/-- **A tame summand's polynomials sum, round by round, from its total to the polynomial in Y at Y's
challenge.** CONDITIONAL on `Tame`. L: the variables' challenges, Y's last. -/
theorem sumsTo_summand (S : Summand) (ds : List Nat) (dY : Nat) (hT : S.Tame ρ ds dY)
    (m L : List E) (hL : L.length = S.vars + 1) :
    SumsTo ρ (ds.map Var.plain ++ [.point zeroE (dY + 1)])
      (fun past => if past.length < ds.length then S.round past else S.inY past m) [] L
      (ρ.val S.total)
      (ρ.val (valueAt (padTo (dY + 1) (S.inY (L.take S.vars) m)) (L.getD S.vars zeroE))) := by
  have hlen : (ds.map Var.plain ++ [Var.point zeroE (dY + 1)]).length = L.length := by
    rw [List.length_append, List.length_map, List.length_singleton, hT.vars, hL]
  have key := sumsTo_of_vals ρ
    (fun past => if past.length < ds.length then S.round past else S.inY past m)
    (valY ρ S dY m) (ds.map Var.plain ++ [.point zeroE (dY + 1)]) [] L hlen ?_
  · have v0 : valY ρ S dY m [] = ρ.val S.total := by
      exact (if_pos (Nat.zero_le _)).trans (S.val_nil ρ)
    have v1 : valY ρ S dY m ([] ++ L) =
        ρ.val (valueAt (padTo (dY + 1) (S.inY (L.take S.vars) m)) (L.getD S.vars zeroE)) := by
      unfold valY
      rw [List.nil_append, if_neg (by omega)]
    rw [v0, v1] at key
    exact key
  · intro i hi
    rw [hlen, hL] at hi
    have htk : (L.take i).length = i := by
      rw [List.length_take]
      omega
    simp only [List.nil_append]
    by_cases hiv : i < S.vars
    · -- a variable's round
      have hv : (ds.map Var.plain ++ [Var.point zeroE (dY + 1)]).getD i (.plain 0) =
          .plain (ds.getD i 0) := getD_map_append_lt Var.plain 0 _ ds i (by rw [hT.vars]; exact hiv)
      have hcut : ∀ j, ds.getD i 0 ≤ j → ρ.val ((S.round (L.take i)).getD j zeroE) = 0 := by
        have := hT.cut (L.take i) (by rw [htk]; exact hiv)
        rwa [htk] at this
      rw [hv, htk, if_pos (by rw [hT.vars]; exact hiv)]
      show ρ.val (sumOf (.plain (ds.getD i 0)) (padTo (ds.getD i 0) (S.round (L.take i)))) = _ ∧
        ρ.val (valueAt (padTo (ds.getD i 0) (S.round (L.take i))) (L.getD i zeroE)) = _
      rw [sumOf_plain ρ _ _ (padTo_length _ _), value_padTo_cut ρ _ _ hcut,
        value_padTo_cut ρ _ _ hcut, value_padTo_cut ρ _ _ hcut,
        S.round_sum ρ hT.uniform _ (by rw [htk]; exact hiv),
        S.round_at ρ hT.uniform _ _ (by rw [htk]; exact hiv) (hT.coef _) (hT.fact _),
        take_succ_getD zeroE L i (by omega)]
      unfold valY
      rw [if_pos (by omega), if_pos (by rw [List.length_append, htk, List.length_singleton]; omega)]
      exact ⟨rfl, rfl⟩
    · -- Y's round
      have hie : i = S.vars := by omega
      subst hie
      have hv : (ds.map Var.plain ++ [Var.point zeroE (dY + 1)]).getD S.vars (.plain 0) =
          .point zeroE (dY + 1) := by
        have := getD_at (Var.plain 0) (Var.point zeroE (dY + 1)) (ds.map Var.plain) []
        rwa [List.length_map, hT.vars] at this
      have hcut := hT.cutY (L.take S.vars) m htk
      rw [hv, htk, if_neg (by rw [hT.vars]; exact Nat.lt_irrefl _)]
      show ρ.val (sumOf (.point zeroE (dY + 1)) (padTo (dY + 1) (S.inY (L.take S.vars) m))) = _ ∧
        ρ.val (valueAt (padTo (dY + 1) (S.inY (L.take S.vars) m)) (L.getD S.vars zeroE)) = _
      rw [sumOf_point0 ρ _ _ (padTo_length _ _), value_padTo_cut ρ _ _ hcut, S.inY_zero ρ,
        ← S.val_full ρ _ htk, List.take_of_length_le (Nat.le_of_eq hL)]
      unfold valY
      rw [if_pos (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩

/-- **What the law of the masked sumcheck's honest part leaves to its caller, of a job made of a
tame summand.** CONDITIONAL on: the call's variables are all summed plainly, with ds coefficients;
it has ends; the summand at this input and front is tame at these numbers; rs has a challenge for
each variable. From the summand's total to the polynomial in Y, cut or filled, at beta. -/
theorem sumsTo_of_tame (k : Call) (ds : List Nat) (e : Ends) (lead : W → Front X → List E)
    (S : W → Front X → Summand) (w : W) (fr : Front X) (hvs : k.vs = ds.map Var.plain)
    (he : k.ends = some e) (hT : (S w fr).Tame ρ ds e.dY) (m rs : List E) (beta : E)
    (hl : rs.length = (S w fr).vars) :
    SumsTo ρ k.all (jobPoly (jobOf k lead S) w fr m) [] (rs ++ [beta]) (ρ.val (S w fr).total)
      (ρ.val (valueAt (padTo (e.dY + 1) ((S w fr).inY rs m)) beta)) := by
  have h := sumsTo_summand ρ (S w fr) ds e.dY hT m (rs ++ [beta])
    (by rw [List.length_append, List.length_singleton, hl])
  rw [← hl, List.take_left, getD_at] at h
  have ha : k.all = ds.map Var.plain ++ [.point zeroE (e.dY + 1)] := by
    unfold Call.all
    rw [he, hvs]
  have hp : jobPoly (jobOf k lead S) w fr m =
      fun past => if past.length < ds.length then (S w fr).round past else (S w fr).inY past m := by
    funext past
    rw [jobPoly_jobOf, hvs, List.length_map]
  rw [ha, hp]
  exact h

/-- **The same, at the challenges as one list**, as a hearing yields them: L has the variables'
challenges, Y's last. CONDITIONAL as `sumsTo_of_tame`. -/
theorem sumsTo_of_tame_at (k : Call) (ds : List Nat) (e : Ends) (lead : W → Front X → List E)
    (S : W → Front X → Summand) (w : W) (fr : Front X) (hvs : k.vs = ds.map Var.plain)
    (he : k.ends = some e) (hT : (S w fr).Tame ρ ds e.dY) (m L : List E)
    (hL : L.length = (S w fr).vars + 1) :
    SumsTo ρ k.all (jobPoly (jobOf k lead S) w fr m) [] L (ρ.val (S w fr).total)
      (ρ.val (valueAt (padTo (e.dY + 1) ((S w fr).inY (L.take (S w fr).vars) m))
        (L.getD (S w fr).vars zeroE))) := by
  have hs : L = L.take (S w fr).vars ++ [L.getD (S w fr).vars zeroE] := by
    rw [← take_succ_getD zeroE L _ (by omega), List.take_of_length_le (Nat.le_of_eq hL)]
  have h := sumsTo_of_tame ρ k ds e lead S w fr hvs he hT m (L.take (S w fr).vars)
    (L.getD (S w fr).vars zeroE) (by rw [List.length_take]; omega)
  rwa [← hs] at h

/-- **That last value is the summand's formula on each end value plus beta times its mask entry.**
CONDITIONAL on `Tame`'s clause on Y. -/
theorem last_is_formula (S : Summand) (ds : List Nat) (dY : Nat) (hT : S.Tame ρ ds dY)
    (m rs : List E) (beta : E) (hl : rs.length = S.vars) :
    ρ.val (valueAt (padTo (dY + 1) (S.inY rs m)) beta) =
      S.formula ρ rs fun n => ρ.val (S.endAt rs n) + ρ.val beta * ρ.val (m.getD n zeroE) := by
  rw [value_padTo_cut ρ _ _ (hT.cutY rs m hl), S.inY_at ρ]

/-- The same, at the challenges as one list. CONDITIONAL on `Tame`'s clause on Y. -/
theorem last_is_formula_at (S : Summand) (ds : List Nat) (dY : Nat) (hT : S.Tame ρ ds dY)
    (m L : List E) (hL : L.length = S.vars + 1) :
    ρ.val (valueAt (padTo (dY + 1) (S.inY (L.take S.vars) m)) (L.getD S.vars zeroE)) =
      S.formula ρ (L.take S.vars) fun n => ρ.val (S.endAt (L.take S.vars) n) +
        ρ.val (L.getD S.vars zeroE) * ρ.val (m.getD n zeroE) :=
  last_is_formula ρ S ds dY hT m _ _ (by rw [List.length_take]; omega)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.jobPoly_jobOf
#print axioms ProofFile.Honest.K5.withPoints_nil
#print axioms ProofFile.Honest.K5.callAt_jobOf
#print axioms ProofFile.Honest.K5.polyOf_padTo_cut
#print axioms ProofFile.Honest.K5.value_padTo_cut
#print axioms ProofFile.Honest.K5.sumOf_plain
#print axioms ProofFile.Honest.K5.sumOf_point0
#print axioms ProofFile.Honest.K5.Lists.getD_map_append_lt
#print axioms ProofFile.Honest.K5.Lists.take_succ_getD
#print axioms ProofFile.Honest.K5.sumsTo_summand
#print axioms ProofFile.Honest.K5.sumsTo_of_tame
#print axioms ProofFile.Honest.K5.sumsTo_of_tame_at
#print axioms ProofFile.Honest.K5.last_is_formula
#print axioms ProofFile.Honest.K5.last_is_formula_at
