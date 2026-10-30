-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FitMergeZero.lean: CONDITIONAL on four hypotheses on public
data. Eight statements with their proofs.

What is here. The three clauses of `k4MakersFit` (Honest/K4/Part.lean) on the merge, AS THE TEST
TYPES THEM, at the zero input and the zero challenges in front of the merge's sumcheck: the job is
made and has its call's shape; the list has the plan's number of claims; each claim passes the
verifier's test on a claim's sizes. FROM FOUR HYPOTHESES ON PUBLIC DATA: `claimsB` (a test with code
on the plan, Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean); that the structure which the
verifier's forms read is made there; `k4LookFits` at fo; `k4TokensFit` at as many zero tokens as the
layout counts. How. Law/FitMerge.lean has the three at every input and all sampled values of four
sizes. Here these four sizes are shown at the zero challenges, with no hypothesis: the challenges of
the second token sumcheck and of the batched sumcheck, and in the first group the embedding's two
points: each round that makes them stands in front of the merge's sumcheck, and the zero challenges
hold as many elements as the verifier's table of rounds says.

  `zero_elems`   at the zero challenges a round's elements are as many as the table says
  `zero_take_len`   how many zero challenges stand in front of the merge's sumcheck
  `rt_zero`, `rs_zero`, `ZE_zero`, `tkh_zero`   the four sizes
  `zk_of_look`   `k4LookFits` has the test on the calls' points
  `merge_zero`   **the three clauses, as the test types them**

Not shown here. THE FOUR HYPOTHESES; the laws named behind them are not called here: that `claimsB`
is true (`claimsB_plan`, Johnson/Road/K4/C/ClaimsBPlan.lean, has it from facts on the plan); that
`envOf` returns (`envOf_pub`, Johnson/Road/K4/C/RowMapsOf.lean); that a value fo passes `k4LookFits`
(`lookFits_zero`, Law/MakersFitMember.lean, has one where la is at most dT, which the test itself
asks); that 0 is below the vocabulary's size. RETURNS AND SIZES ALONE. The twelve other clauses of
`k4MakersFit` are not here (four of them: Law/FitPowers.lean). Nothing on soundness, on completeness
or on any other property.

Kin. `rt_zero` and `rs_zero` end as `pts_rt` and `pts_rs` (Johnson/Desc/K4/Honest/Law/PtsSizes.lean)
end, at the zero input and the zero challenges in front of the merge's sumcheck; those two ask a
count in other letters and are not called here. `rt_zero_at` and `rs_zero_at` (Law/ZeroSizes.lean
(no part of the library yet)) state both again, at k = 6. Sought: by statement, to the letter and up
to the bound letters, among the theorems of the library and of files that are no part of it yet, as
they lay with the writer: no hit; by short name: `merge_zero` stands also in Hiop/WholeProof.lean:
read: another matter.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FitMerge
import Johnson.Desc.ProofFile.Honest.K4.Law.FitPowers
import Johnson.Desc.ProofFile.Honest.K4.Law.SumAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (RoundName Forest.Heard wsClaimShape)
open OnBytes.Desc.First.K4 (Rd rounds masked layerRds pointRd batchRd k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw (inner_size)
open OnBytes.Desc.First.K4.RtPub (claimsB zkFits)

/-- At the zero challenges a round's elements are as many as the table says. -/
theorem zero_elems (Q : K4Pub) (j : Nat) (d : Rd) (hd : (rounds Q.P Q.hp Q.g)[j]? = some d) :
    (elemsAt (k4ZeroOwn Q) j).size = d.drawn := by
  unfold elemsAt k4ZeroOwn
  rw [List.getElem?_map, hd]
  show (elemsOf ⟨List.replicate d.drawn zeroE.triple, [], [], none⟩).size = _
  simp [elemsOf]

variable (Q : K4Pub) (fo : Forest.Heard)

/-- The first so many zero challenges as stand in front of the merge's sumcheck are so many. -/
theorem zero_take_len :
    ((k4ZeroOwn Q).take (k4StartAt Q 6)).length = k4StartAt Q 6 := by
  have s : (starts Q).getD 6 0 = k4StartAt Q 6 := by rw [starts_eq]; rfl
  have h := starts_le Q 6
  rw [s] at h
  rw [List.length_take, k4ZeroOwn, List.length_map]
  omega

/-- The challenges of the second token sumcheck. -/
theorem rt_zero : (k4ZeroPts Q fo ((starts Q).getD 6 0)).rt.size = Q.P.y.h.lt := by
  have s : (starts Q).getD 6 0 = k4StartAt Q 6 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_rt_val, drop_take_rep, s]
  unfold innerAt
  refine inner_size _ _ _ ?_
  rw [zero_take_len]
  simp only [k4StartAt]
  omega

/-- The challenges of the batched sumcheck. -/
theorem rs_zero : (k4ZeroPts Q fo ((starts Q).getD 6 0)).rs.size = Q.hp.lamS := by
  have s : (starts Q).getD 6 0 = k4StartAt Q 6 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_rs_val, drop_take_rep, s, Array.size_reverse]
  unfold innerAt
  refine inner_size _ _ _ ?_
  rw [zero_take_len]
  simp only [k4StartAt]
  omega

/-- The embedding's first point; empty outside the first group. -/
theorem ZE_zero : (k4ZeroPts Q fo ((starts Q).getD 6 0)).ZE.size =
    (if (Q.g == 0) = true then Q.P.y.ls + Q.P.y.h.lt else 0) := by
  have s : (starts Q).getD 6 0 = k4StartAt Q 6 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_ZE_val, drop_take_rep, s]
  by_cases hg : (Q.g == 0) = true
  · rw [if_pos hg, if_pos hg, elemsAt_take _ _ _ (by simp only [k4StartAt]; omega)]
    refine zero_elems Q 1 (pointRd .zero (Q.P.y.ls + Q.P.y.h.lt)) ?_
    simp [rounds, hg]
  · rw [if_neg hg, if_neg hg]
    rfl

/-- The embedding's second point; empty outside the first group. -/
theorem tkh_zero : (k4ZeroPts Q fo ((starts Q).getD 6 0)).tkh.size =
    (if (Q.g == 0) = true then Q.P.y.lPd - Q.P.y.ls else 0) := by
  have s : (starts Q).getD 6 0 = k4StartAt Q 6 := by rw [starts_eq]; rfl
  unfold k4ZeroPts k4ZeroHeard
  rw [pts_tkh_val, drop_take_rep, s]
  by_cases hg : (Q.g == 0) = true
  · rw [if_pos hg, if_pos hg, elemsAt_take _ _ _ (by simp only [k4StartAt]; omega)]
    refine zero_elems Q 2 (pointRd .zero (Q.P.y.lPd - Q.P.y.ls)) ?_
    simp [rounds, hg]
  · rw [if_neg hg, if_neg hg]
    rfl

variable {Q fo}

/-- `k4LookFits` has the test on the calls' points. -/
theorem zk_of_look (h : k4LookFits Q fo = true) : zkFits Q.P fo.zk = true := by
  unfold k4LookFits at h
  simp only [Bool.and_eq_true] at h
  unfold zkFits
  rw [Bool.and_eq_true]
  exact ⟨h.1.2, h.2⟩

/-- CONDITIONAL on the four premises named. **THE THREE CLAUSES ON THE MERGE, AS `k4MakersFit` TYPES
THEM.** -/
theorem merge_zero {v : OnBytes.Model.Layer.Env} (hB : claimsB Q.P Q.hp Q.g = true)
    (hv : envOf Q (k4ZeroPts Q fo ((starts Q).getD 6 0)) = some v) (hL : k4LookFits Q fo = true)
    (ht : k4TokensFit Q (Array.replicate Q.P.y.T 0) = true) :
    ((jobMerge Q (k4ZeroIn Q fo) (k4ZeroPts Q fo ((starts Q).getD 6 0))).any
        (k4JobFits ((k4Shapes Q).getD 6 ⟨0, [], none⟩)) = true) ∧
      ((mergeClaimsAt Q (k4ZeroIn Q fo) (k4ZeroPts Q fo ((starts Q).getD 6 0))).any
        (fun l => l.length == Q.hp.NCL) = true) ∧
      ((mergeClaimsAt Q (k4ZeroIn Q fo) (k4ZeroPts Q fo ((starts Q).getD 6 0))).any
        (fun l => l.all fun c => (wsClaimShape Q.P.wsLay c).isOk) = true) := by
  have hz : zkFits Q.P (k4ZeroPts Q fo ((starts Q).getD 6 0)).fo.zk = true := zk_of_look hL
  have ht' : k4TokensFit Q (k4ZeroIn Q fo).tokv = true := ht
  obtain ⟨j, hj, hf⟩ := merge_fit (w := k4ZeroIn Q fo) hB hv hz ht' (rs_zero Q fo) (rt_zero Q fo)
    (ZE_zero Q fo) (tkh_zero Q fo)
  obtain ⟨cls, hc, hn, hs⟩ := merge_claims_fit (w := k4ZeroIn Q fo) hB hv hz ht' (rs_zero Q fo)
    (rt_zero Q fo) (ZE_zero Q fo) (tkh_zero Q fo)
  refine ⟨?_, ?_, ?_⟩
  · rw [hj]
    exact hf
  · rw [hc]
    show (cls.length == Q.hp.NCL) = true
    rw [hn]
    exact beq_self_eq_true _
  · rw [hc]
    exact List.all_eq_true.2 hs

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.zero_elems
#print axioms ProofFile.Honest.K4.zero_take_len
#print axioms ProofFile.Honest.K4.rt_zero
#print axioms ProofFile.Honest.K4.rs_zero
#print axioms ProofFile.Honest.K4.ZE_zero
#print axioms ProofFile.Honest.K4.tkh_zero
#print axioms ProofFile.Honest.K4.zk_of_look
#print axioms ProofFile.Honest.K4.merge_zero
