-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/ReadsAtt.lean: at an attention segment, the number of reads that `readsB` counts at the
tables `attPairs` (both in Johnson/Desc/First/Link/K9RowsAsk.lean) is the number of reads that the planner counts
(`Attention.tableReads`, OnBytes/Model/AttentionPlan.lean), at every plan that the planner returns.
Statements with their proofs; no definition; nothing is evaluated.

How. Every table's matrix has a number below NAs + 4 (`att_pairs_below`), so the double loop of `readsB` is one sum with
a term for each table: the rows of the table's matrix divided by the table's rows in a block, rounded down
(`readsB_flat`, Johnson/Desc/K9/Honest/LensPaid/ReadsFlat.lean). The list of tables has five families. The sum over it
of a weight that is the same at all parts of the matrix `as` is written out family by family (`sum_att_by`, after
`sum_att`, Johnson/Desc/First/Link/Law/K9PosAttPaid.lean). The rows of the five sorts of matrix are read off the
planner's list `Attention.matrices` (`rows_as` to `rows_qa`, by `matrices_as`,
Johnson/Goal/Meaning/HidPlanSizes.lean, and `tail_at`, Johnson/Desc/First/Link/Law/AttTabEntries.lean). The families
give 3 NAs times 1, (k + 6) times wcH, once wcO T / 2 ^ la, (2 k + 5) times wcQ T / 2 ^ la, and 3 times 1. Here k is the
number of units of the scores, which is the planner's nKFp (`units_is`,
Johnson/Desc/K9/Honest/LensPaid/UnitsIs.lean).

  `sum_rep_by`, `sum_parts_by`, `sum_att_by`   the sum of a weight over the list `attTriples`
  `att_pairs_below`   every table's matrix has a number below NAs + 4
  `rows_as`, `rows_ah`, `rows_ao`, `rows_bA`, `rows_qa`   the rows of the matrices
  `reads_att_at`   the equality at the planner's list of matrices as the plan stores it: each matrix under `fixed`
      (Johnson/Road/Lane5AttLabel.lean), which leaves the rows (`fixed_m`); for every shape S with 0 < S.T and every
      input i
  `plan_tokens_pos`   at a plan that `Attention.plan` returns, T is a power of two, so it is not 0 (`Shaped.T`,
      Johnson/Road/Lane5AttShape.lean)
  `reads_att_eq`   the equality at a plan A0 that `Attention.plan` returns: its NM by `plan_nm`
      (Johnson/Desc/First/Att/Claims/PlanU3.lean), its matrices by `plan_mats` (Johnson/Road/Lane5AttLabel.lean)
  `reads_att_public`   the same at a plan that stands in the public parameters W, under the premise `PlanIs W`
      (Johnson/Desc/First/Att/GuardPublic.lean): each stored plan is a return of the planner but for one field, which
      the equality does not read

Limits. `PlanIs W` is a premise here; `planIs_public`, in the file that defines it, proves it at every return of
`publicOf`. `reads_att_at` has the premise 0 < S.T: by reading, at T = 0 with wcH not 0 the two numbers differ; no
theorem here says so. Nothing is said on the plan's number of claims. No property of the protocol is claimed: nothing is
said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.First.Link.Law.K9PosAttPaid
import Johnson.Desc.First.Att.Claims.PlanU3
import Johnson.Desc.First.Att.GuardPublic
import Johnson.Desc.K9.Honest.LensPaid.ReadsFlat
import Johnson.Desc.K9.Honest.LensPaid.UnitsIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9

open OnBytes OnBytes.Model
open OnBytes.Road.L5 (fixed plan_mats plan_shape shaped_of_hid)
open VerifiableInference.Desc.K9Asks (readsB repB attTriples attPairs mem_att fixed_m fixed_k tail_at)
open VerifiableInference.Desc.First.Att.P (PlanIs)

/-! ## 1 The sum of a weight over the list of tables -/

/-- The sum of a weight over a list laid k times is k times the sum over the list. -/
theorem sum_rep_by (w : ℕ × ℕ × ℕ → ℕ) (l : List (ℕ × ℕ × ℕ)) :
    ∀ k, ((repB k l).map w).sum = k * (l.map w).sum
  | 0 => by simp [repB]
  | k + 1 => by
    show ((l ++ repB k l).map w).sum = _
    rw [List.map_append, List.sum_append, sum_rep_by w l k, Nat.succ_mul, Nat.add_comm]

/-- Where the weight is c at each of n tables that differ in the matrix's number alone, the sum is n times c. -/
theorem sum_parts_by (w : ℕ × ℕ × ℕ → ℕ) (a b c : ℕ) :
    ∀ n, (∀ q < n, w (q, a, b) = c) → (((List.range n).flatMap fun q => [(q, a, b)]).map w).sum = n * c
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append,
      sum_parts_by w a b c n fun q hq => h q (by omega)]
    simp [Nat.succ_mul, h n (by omega)]

/-- The sum of a weight over an attention segment's tables, family by family, from the weight's five values. -/
theorem sum_att_by (S : Attention.Shape) (k : ℕ) (w : ℕ × ℕ × ℕ → ℕ) {cA cH cO cQ cB : ℕ}
    (hA : ∀ q < S.cf.NAs, w (q, 2 ^ S.cf.lmS, S.kAs / S.cf.NAs) = cA)
    (hH : w (S.cf.NAs, S.T, S.fillH) = cH)
    (hO : w (S.cf.NAs + 1, 2 ^ S.cf.la, S.fillO * S.T / 2 ^ S.cf.la) = cO)
    (hQ : w (S.cf.NAs + 3, 2 ^ S.cf.la, S.fillQ * S.T / 2 ^ S.cf.la) = cQ)
    (hB : w (S.cf.NAs + 2, 2 ^ S.cf.lmb, S.kbA) = cB) :
    ((attTriples S k).map w).sum =
      3 * (S.cf.NAs * cA) + (k + 6) * cH + cO + (2 * k + 5) * cQ + 3 * cB := by
  have hP := sum_parts_by w (2 ^ S.cf.lmS) (S.kAs / S.cf.NAs) cA S.cf.NAs hA
  unfold attTriples
  simp only [List.map_append, List.sum_append, sum_rep_by, hP, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hH, hO, hQ, hB]
  ring

/-- Every table's matrix has a number below NAs + 4. -/
theorem att_pairs_below (S : Attention.Shape) : ∀ t ∈ attPairs S, t.1 < S.cf.NAs + 4 := by
  intro t ht
  unfold attPairs at ht
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
  rcases mem_att hx with ⟨q, hq, rfl⟩ | rfl | rfl | rfl | rfl
  · show q < S.cf.NAs + 4
    omega
  · show S.cf.NAs < S.cf.NAs + 4
    omega
  · show S.cf.NAs + 1 < S.cf.NAs + 4
    omega
  · show S.cf.NAs + 3 < S.cf.NAs + 4
    omega
  · show S.cf.NAs + 2 < S.cf.NAs + 4
    omega

/-! ## 2 The rows of the matrices -/

/-- Each of the first NAs matrices of the list, the parts of the matrix `as`, has 2 ^ lmS rows. -/
theorem rows_as (S : Attention.Shape) (i : Attention.In) {q : ℕ} (hq : q < S.cf.NAs) :
    (((Attention.matrices S i).map fixed).getD q {}).m = 2 ^ S.cf.lmS := by
  obtain ⟨M, hM, hm, -⟩ := _root_.Meaning.matrices_as S i hq
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, hM]
  exact (fixed_m M).trans hm

/-- Number NAs of the list, the matrix ah, has wcH T rows. -/
theorem rows_ah (S : Attention.Shape) (i : Attention.In) :
    (((Attention.matrices S i).map fixed).getD S.cf.NAs {}).m = S.cf.wcH * S.T := by
  obtain ⟨e1, -⟩ := tail_at fixed fixed_m fixed_k S i 0 _ rfl
  rw [Nat.add_zero] at e1
  exact e1

/-- Number NAs + 1 of the list, the matrix ao, has wcO T rows. -/
theorem rows_ao (S : Attention.Shape) (i : Attention.In) :
    (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 1) {}).m = S.cf.wcO * S.T := by
  obtain ⟨e1, -⟩ := tail_at fixed fixed_m fixed_k S i 1 _ rfl
  exact e1

/-- Number NAs + 2 of the list, the matrix bA, has 2 ^ lmb rows. -/
theorem rows_bA (S : Attention.Shape) (i : Attention.In) :
    (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 2) {}).m = 2 ^ S.cf.lmb := by
  obtain ⟨e1, -⟩ := tail_at fixed fixed_m fixed_k S i 2 _ rfl
  exact e1

/-- Number NAs + 3 of the list, the matrix qa, has wcQ T rows. -/
theorem rows_qa (S : Attention.Shape) (i : Attention.In) :
    (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 3) {}).m = S.cf.wcQ * S.T := by
  obtain ⟨e1, -⟩ := tail_at fixed fixed_m fixed_k S i 3 _ rfl
  exact e1

/-! ## 3 The reads -/

/-- Where T is not 0, the reads that `readsB` counts over the planner's list of matrices are the planner's number. -/
theorem reads_att_at (S : Attention.Shape) (i : Attention.In) (hT : 0 < S.T) :
    readsB (S.cf.NAs + 4) ((Attention.matrices S i).map fixed) (attPairs S) =
      Attention.tableReads S (Attention.Counts.of S) := by
  rw [readsB_flat _ _ _ (att_pairs_below S)]
  unfold attPairs
  rw [List.map_map, units_is]
  refine (sum_att_by S _ _ (cA := 1) (cH := S.cf.wcH) (cO := S.cf.wcO * S.T / 2 ^ S.cf.la)
    (cQ := S.cf.wcQ * S.T / 2 ^ S.cf.la) (cB := 1) ?_ ?_ ?_ ?_ ?_).trans ?_
  · intro q hq
    show (((Attention.matrices S i).map fixed).getD q {}).m / 2 ^ S.cf.lmS = 1
    rw [rows_as S i hq]
    exact Nat.div_self (Nat.two_pow_pos _)
  · show (((Attention.matrices S i).map fixed).getD S.cf.NAs {}).m / S.T = S.cf.wcH
    rw [rows_ah]
    exact Nat.mul_div_cancel _ hT
  · show (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 1) {}).m / 2 ^ S.cf.la =
      S.cf.wcO * S.T / 2 ^ S.cf.la
    rw [rows_ao]
  · show (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 3) {}).m / 2 ^ S.cf.la =
      S.cf.wcQ * S.T / 2 ^ S.cf.la
    rw [rows_qa]
  · show (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb = 1
    rw [rows_bA]
    exact Nat.div_self (Nat.two_pow_pos _)
  · show _ = 3 * S.cf.NAs + ((Attention.Counts.of S).nKFp + 6) * S.cf.wcH + S.cf.wcO * S.T / 2 ^ S.cf.la +
      (2 * (Attention.Counts.of S).nKFp + 5) * (S.cf.wcQ * S.T / 2 ^ S.cf.la) + 3
    omega

/-- At a plan that the planner returns, the number of tokens is not 0. -/
theorem plan_tokens_pos {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A0 : Attention.Plan}
    (h0 : Attention.plan settings i cf = .ok A0) : 0 < A0.S.T := by
  rw [(shaped_of_hid (plan_shape h0).1).T]
  exact Nat.two_pow_pos _

/-- **At a plan that the planner returns, the reads that `readsB` counts are the planner's number of reads.** -/
theorem reads_att_eq {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A0 : Attention.Plan}
    (h0 : Attention.plan settings i cf = .ok A0) :
    readsB A0.seam.tl.NM A0.seam.tl.mats (attPairs A0.S) =
      Attention.tableReads A0.S (Attention.Counts.of A0.S) := by
  rw [_root_.K5Law.plan_nm h0, plan_mats h0]
  exact reads_att_at A0.S A0.inp (plan_tokens_pos h0)

/-- **The same at a plan that stands in the public parameters, where `PlanIs` holds of them.** -/
theorem reads_att_public {W : Verify.Public} (hP : PlanIs W) {g : ℕ} {a : Attention.Plan}
    (ha : W.A[g]? = some a) :
    readsB a.seam.tl.NM a.seam.tl.mats (attPairs a.S) =
      Attention.tableReads a.S (Attention.Counts.of a.S) := by
  obtain ⟨A0, pf, h0, e⟩ := hP g a ha
  have eS : a.S = A0.S := by rw [e]
  have eM : a.seam.tl.mats = A0.seam.tl.mats := by rw [e]
  have eN : a.seam.tl.NM = A0.seam.tl.NM := by rw [e]
  rw [eS, eM, eN]
  exact reads_att_eq h0

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.sum_rep_by
#print axioms ProofFile.Honest.K9.sum_parts_by
#print axioms ProofFile.Honest.K9.sum_att_by
#print axioms ProofFile.Honest.K9.att_pairs_below
#print axioms ProofFile.Honest.K9.rows_as
#print axioms ProofFile.Honest.K9.rows_ah
#print axioms ProofFile.Honest.K9.rows_ao
#print axioms ProofFile.Honest.K9.rows_bA
#print axioms ProofFile.Honest.K9.rows_qa
#print axioms ProofFile.Honest.K9.reads_att_at
#print axioms ProofFile.Honest.K9.plan_tokens_pos
#print axioms ProofFile.Honest.K9.reads_att_eq
#print axioms ProofFile.Honest.K9.reads_att_public
