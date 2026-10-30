-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/PairSumsTo.lean: THE LAW OF A SUM OF WEIGHTED PRODUCTS OF PAIRS OF
MAPS (Johnson/Desc/K6/Honest/PairLaw.lean), IN THE TERMS IN WHICH THE LAW OF THE MASKED SUMCHECK's
HONEST PART ASKS IT OF A CALLER: SumsTo. Two definitions; statements with their proofs.

WHAT IT IS NOT. One list of challenges at a time. That a caller's claimed form is worth the sum, and
that the verifier's end term is the summand on what was shown, are the caller's to show. Nothing on
any property of a protocol. No chance in it. The tests by evaluation lie in a file apart,
PairSumsToTest.lean, which is not in the library.

Of the folder Johnson/Desc/ProofFile/Honest/SumLaw/ it uses Terms.lean (SumsTo, jobPoly) and
More.lean (sumsTo_of_vals).

  headPairVars, headPairPoly   a sum's variables, the further variable last; its polynomial of the
                        round behind the challenges passed
  headPair_vals         CONDITIONAL on one challenge more than the sum has points: the two premises
                        of sumsTo_of_vals, to the letter, at the claim PairSum.valK
  headPair_sumsTo       CONDITIONAL on the same count: from the sum to the summand at the
                        challenges, for every sum
  headPair_sumsTo_job   CONDITIONAL on the same count: the same at a job's own call and
                        polynomials, under five premises on the job: its shape has as many
                        variables as the sum has points, all summed at one and the same stand-in
                        point a, three coefficients each (hvs); two coefficients are sent in the
                        further variable (he); its points, round polynomials and polynomial in the
                        further variable are the sum's (hp, hr, hy)
All else is a helper.
-/
import Johnson.Desc.K6.Honest.PairLaw
import Johnson.Desc.ProofFile.Honest.SumLaw.More

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE oneE addE mulE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (Var Call valueAt)
open VerifiableInference.Desc.Kinds.Head.Honest (PairSum exists_three round_length inY_length
  round_sums round_at inY_zero inY_at total_reads valK_le valK_gt)
open SumLaw (SumsTo jobPoly)

variable {W X : Type}

/-- The variables of a sum's call: each summed at its point, three coefficients; the further
variable, read at 0, last. -/
def headPairVars (s : PairSum) : List Var :=
  (s.z.map fun x => Var.point x 3) ++ [Var.point zeroE 3]

/-- The summand's polynomial of the round behind the challenges passed. -/
def headPairPoly (s : PairSum) (masks past : List E) : List E :=
  if past.length < s.z.length then s.round past else s.inY past masks

/-! ## Helpers -/

theorem headVars_lt : ∀ (zs : List E) (i : Nat), i < zs.length →
    ((zs.map fun x => Var.point x 3) ++ [Var.point zeroE 3]).getD i (.plain 0) =
      .point (zs.getD i zeroE) 3
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: zs, i + 1, h => headVars_lt zs i (Nat.lt_of_succ_lt_succ h)

theorem headVars_last : ∀ zs : List E,
    ((zs.map fun x => Var.point x 3) ++ [Var.point zeroE 3]).getD zs.length (.plain 0) =
      .point zeroE 3
  | [] => rfl
  | _ :: zs => headVars_last zs

theorem headVars_length (s : PairSum) : (headPairVars s).length = s.z.length + 1 := by
  unfold headPairVars
  rw [List.length_append, List.length_map, List.length_singleton]

theorem head_take_snoc : ∀ (l : List E) (i : Nat), i < l.length →
    l.take (i + 1) = l.take i ++ [l.getD i zeroE]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | x :: l, i + 1, h => congrArg (x :: ·) (head_take_snoc l i (Nat.lt_of_succ_lt_succ h))

/-- Three coefficients, summed at a point. -/
theorem head_sumOf_three (z a b c : E) :
    Reading.gl.val (sumOf (.point z 3) (padTo 3 [a, b, c])) =
      Reading.gl.val a + Reading.gl.val z * (Reading.gl.val b + Reading.gl.val c) := by
  show Reading.gl.val (addE (addE (addE zeroE (mulE a oneE)) (mulE b z)) (mulE c z)) = _
  rw [Reading.gl.add, Reading.gl.add, Reading.gl.add, Reading.gl.mul, Reading.gl.mul,
    Reading.gl.mul, Reading.gl.zero, Reading.gl.one]
  ring

/-- **The two premises on partial sums**, at every variable: the round's list, summed, is the claim
behind the challenges passed, and its value at the challenge is the next claim. -/
theorem headPair_vals (s : PairSum) (masks rs : List E) (h : rs.length = s.z.length + 1) :
    ∀ i, i < (headPairVars s).length →
      Reading.gl.val (sumOf ((headPairVars s).getD i (.plain 0))
          (padTo ((headPairVars s).getD i (.plain 0)).d (headPairPoly s masks ([] ++ rs.take i))))
        = s.valK masks ([] ++ rs.take i) ∧
      Reading.gl.val (valueAt
          (padTo ((headPairVars s).getD i (.plain 0)).d (headPairPoly s masks ([] ++ rs.take i)))
          (rs.getD i zeroE)) = s.valK masks ([] ++ rs.take (i + 1)) := by
  intro i hi
  rw [headVars_length] at hi
  rw [List.nil_append, List.nil_append]
  have hir : i < rs.length := by omega
  have hti : (rs.take i).length = i := by
    rw [List.length_take]
    omega
  rcases Nat.lt_or_ge i s.z.length with hlt | hge
  · have hlt' : (rs.take i).length < s.z.length := by
      rw [hti]
      exact hlt
    have hv : (headPairVars s).getD i (.plain 0) = .point (s.z.getD i zeroE) 3 :=
      headVars_lt s.z i hlt
    have hp : headPairPoly s masks (rs.take i) = s.round (rs.take i) := if_pos hlt'
    obtain ⟨a, b, c, hg⟩ := exists_three (round_length s (rs.take i))
    have h1 := round_sums s (rs.take i) hlt'
    have h2 := round_at s (rs.take i) (rs.getD i zeroE) hlt'
    rw [hti, hg] at h1
    rw [hg] at h2
    rw [hv, hp, hg, head_take_snoc rs i hir, valK_le s masks _ (le_of_lt hlt'),
      valK_le s masks (rs.take i ++ [rs.getD i zeroE])
        (by rw [List.length_append, List.length_singleton]; omega)]
    exact ⟨(head_sumOf_three _ a b c).trans h1, h2⟩
  · have hin : i = s.z.length := by omega
    subst hin
    have hv : (headPairVars s).getD s.z.length (.plain 0) = .point zeroE 3 := headVars_last s.z
    have hp : headPairPoly s masks (rs.take s.z.length) = s.inY (rs.take s.z.length) masks :=
      if_neg (by rw [hti]; exact Nat.lt_irrefl _)
    obtain ⟨a, b, c, hg⟩ := exists_three (inY_length s (rs.take s.z.length) masks)
    have h1 := inY_zero s (rs.take s.z.length) masks hti
    have h2 := inY_at s (rs.take s.z.length) masks (rs.getD s.z.length zeroE) hti
    rw [hg] at h1 h2
    have hfull : rs.take (s.z.length + 1) = rs := List.take_of_length_le (by omega)
    rw [hv, hp, hg, valK_le s masks _ (le_of_eq hti), hfull, valK_gt s masks rs (by omega)]
    refine ⟨(head_sumOf_three zeroE a b c).trans ?_, h2⟩
    rw [Reading.gl.zero, zero_mul, add_zero]
    exact h1

/-- **Round by round, the polynomials of a sum of weighted products of pairs of maps sum from the
sum to the summand at the challenges.** rs: the variables' challenges, the further variable's last.
-/
theorem headPair_sumsTo (s : PairSum) (masks rs : List E) (h : rs.length = s.z.length + 1) :
    SumsTo Reading.gl (headPairVars s) (headPairPoly s masks) [] rs (Reading.gl.val s.total)
      (s.endK (rs.take s.z.length) masks (rs.getD s.z.length zeroE)) := by
  have hl : (headPairVars s).length = rs.length := by rw [headVars_length, h]
  have key := SumLaw.sumsTo_of_vals Reading.gl (headPairPoly s masks) (s.valK masks)
    (headPairVars s) [] rs hl (headPair_vals s masks rs h)
  rw [List.nil_append, valK_le s masks [] (Nat.zero_le _), ← total_reads,
    valK_gt s masks rs (by omega)] at key
  exact key

/-- Placeholders take the points, where they are as many. -/
theorem head_withPoints_replicate (a : E) : ∀ zs : List E,
    withPoints (List.replicate zs.length (Var.point a 3)) zs = zs.map fun x => Var.point x 3 :=
  fun zs =>
    match zs with
    | [] => rfl
    | z :: zs => congrArg (Var.point z 3 :: ·) (head_withPoints_replicate a zs)

/-- **The same in the terms of a job**, CONDITIONAL on the same count of challenges and on five
premises on the job at this input and front: its shape has as many variables as the sum has points,
all summed at one and the same stand-in point a, three coefficients each; two coefficients are sent
in the further variable; its points, its round polynomials and its polynomial in the further
variable are the sum's. -/
theorem headPair_sumsTo_job (J : SumJob W X) (w : W) (fr : Front X) (s : PairSum) (a : E) (e : Nat)
    (masks rs : List E)
    (hvs : J.shape.vs = List.replicate s.z.length (Var.point a 3))
    (he : J.shape.ends = some ⟨2, e⟩)
    (hp : J.points w fr = s.z)
    (hr : J.round w fr = s.round)
    (hy : J.inY w fr = s.inY)
    (h : rs.length = s.z.length + 1) :
    SumsTo Reading.gl (J.callAt w fr).all (jobPoly J w fr masks) [] rs (Reading.gl.val s.total)
      (s.endK (rs.take s.z.length) masks (rs.getD s.z.length zeroE)) := by
  have hall : (J.callAt w fr).all = headPairVars s := by
    have h1 : (J.callAt w fr).ends = some ⟨2, e⟩ := he
    have h2 : (J.callAt w fr).vs = s.z.map fun x => Var.point x 3 := by
      show withPoints J.shape.vs (J.points w fr) = _
      rw [hvs, hp, head_withPoints_replicate]
    unfold Call.all
    rw [h1, h2]
    rfl
  have hpoly : jobPoly J w fr masks = headPairPoly s masks := by
    funext past
    unfold jobPoly headPairPoly
    rw [hvs, List.length_replicate, hr, hy]
  rw [hall, hpoly]
  exact headPair_sumsTo s masks rs h

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headVars_lt
#print axioms ProofFile.Honest.K6.headVars_last
#print axioms ProofFile.Honest.K6.headVars_length
#print axioms ProofFile.Honest.K6.head_take_snoc
#print axioms ProofFile.Honest.K6.head_sumOf_three
#print axioms ProofFile.Honest.K6.headPair_vals
#print axioms ProofFile.Honest.K6.headPair_sumsTo
#print axioms ProofFile.Honest.K6.head_withPoints_replicate
#print axioms ProofFile.Honest.K6.headPair_sumsTo_job
