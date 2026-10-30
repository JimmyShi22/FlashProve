-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FitMerge.lean: CONDITIONAL. Two statements with their proofs.

What is here. Three of the fifteen clauses of `k4MakersFit` (Honest/K4/Part.lean), the clause on the
makers of the public test on the parts of the feed-forward layers' own rounds (the sub-protocol K4),
GENERAL IN THE INPUT w AND THE SAMPLED VALUES p: the list of claims that the merge joins is made,
has the plan's number of claims, and each passes the verifier's own test on a claim's sizes; and the
merge's job is made and has its call's public shape. FROM: one test with code on the plan alone,
`claimsB` (Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean); that the structure which the verifier's
forms read is made; the sizes of four of p's fields and of the calls' points; the test on the
tokens. How. `claims_of_B` (that file) has the verifier's two functions' returns, the count and the
tests at all challenges of the plan's sizes; `mergeClaimsAt` (Johnson/Desc/K4/Honest/Merge.lean)
calls just these two. The job's shape: `mergeJob_jobFits` (Law/SumMerge.lean), at every list of
claims.

  `merge_claims_fit`   **the list: made, counted, each of the sizes asked**
  `merge_fit`   **the job**, in the form ∃ j, the maker returns j, and j has the call's shape

Not shown here. That `claimsB` is true: a hypothesis here; `claimsB_plan`
(Johnson/Road/K4/C/ClaimsBPlan.lean) has it from facts on the plan, general in the sizes, and
`claimsB_head` (Law/DearX.lean) under the library's hypothesis on the public files. That `envOf`
returns (hv): a hypothesis here; `envOf_pub` (Johnson/Road/K4/C/RowMapsOf.lean) has it from two
public facts. That p's fields have these sizes: at the zero challenges Law/FitMergeZero.lean has it;
at a run's, nothing here (of rs and rt: `pts_rs`, `pts_rt`,
Johnson/Desc/K4/Honest/Law/PtsSizes.lean, once enough of the sub-protocol's own challenges have been
heard). RETURNS AND SIZES ALONE: nothing on a claim's value. Nothing on soundness, on completeness
or on any other property.

Kin. `merge_run` (Law/SumAtRun.lean) ends in `merge_claims_fit`'s three clauses, and in the number
of the powers besides, at the sampled values of a run's challenges: from the public test's yes and
three premises on the challenges, not from `claimsB`; neither law calls the other. Sought: by
statement, to the letter and up to the bound letters, among the theorems of the library and of files
that are no part of it yet, as they lay with the writer: no hit; no short name of the two stands
elsewhere.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMerge
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (WsClaim wsClaimShape)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub (claimsB zkFits claims_of_B)

variable {Q : K4Pub} {w : K4In} {p : Pts} {v : OnBytes.Model.Layer.Env}

/-- CONDITIONAL on every hypothesis named. **THE CLAIMS THAT THE MERGE JOINS: MADE, AS MANY AS THE
PLAN COUNTS, EACH OF THE SIZES THAT THE VERIFIER's TEST ASKS.** -/
theorem merge_claims_fit (hB : claimsB Q.P Q.hp Q.g = true) (hv : envOf Q p = some v)
    (hz : zkFits Q.P p.fo.zk = true) (ht : k4TokensFit Q w.tokv = true)
    (hrs : p.rs.size = Q.hp.lamS) (hrt : p.rt.size = Q.P.y.h.lt)
    (hZ : p.ZE.size = (if (Q.g == 0) = true then Q.P.y.ls + Q.P.y.h.lt else 0))
    (hk : p.tkh.size = (if (Q.g == 0) = true then Q.P.y.lPd - Q.P.y.ls else 0)) :
    ∃ cls, mergeClaimsAt Q w p = some cls ∧ cls.length = Q.hp.NCL ∧
      ∀ c ∈ cls, (wsClaimShape Q.P.wsLay c).isOk = true := by
  have hf : v.y = Q.P.y ∧ v.g = Q.g ∧ v.zk = p.fo.zk := by
    have hv' := hv
    unfold envOf at hv'
    obtain ⟨iU3, _, h1⟩ := Option.bind_eq_some_iff.mp hv'
    obtain ⟨⟨tab, a, b⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain rfl := Option.some.inj h2
    exact ⟨rfl, rfl, rfl⟩
  have hB' : claimsB { Q.P with tokv := w.tokv } Q.hp Q.g = true := hB
  have hz' : zkFits { Q.P with tokv := w.tokv } v.zk = true := by
    rw [hf.2.2]
    exact hz
  obtain ⟨TS, hTS, hall⟩ := claims_of_B (P := { Q.P with tokv := w.tokv }) (v := v) hB' hf.1 hf.2.1
    hz' ht
  obtain ⟨cP, cE, hP, hE, hn, _, _, hs⟩ := hall p.rs p.rt p.ZE p.tkh hrs hrt hZ hk
  refine ⟨cP ++ cE, ?_, ?_, ?_⟩
  · have hTS' : OnBytes.Model.Layer.callsTS Q.P = some TS := hTS
    have hpc : panelClaims Q p = some cP := by
      have e : panelClaims Q p = (claimEnvOf Q p).bind fun ce =>
          (OnBytes.Model.Layer.callsTS Q.P).bind fun TS => ce.weightClaims TS := rfl
      rw [e]
      unfold claimEnvOf
      rw [hv, Option.map_some, Option.bind_some, hTS', Option.bind_some]
      exact hP
    have key : mergeClaimsAt Q w p = (panelClaims Q p).bind fun cp =>
        if (Q.g == 0) = true then
          (Option.map (fun x => [x]) (embClaim Q w p)).bind fun z => some (cp ++ z)
        else (some []).bind fun z => some (cp ++ z) := rfl
    rw [key, hpc, Option.bind_some]
    by_cases hg : (Q.g == 0) = true
    · rw [if_pos hg]
      rw [if_pos hg] at hE
      have hemb : Option.map (fun x => [x]) (embClaim Q w p) = some cE := by
        unfold embClaim claimEnvOf
        rw [if_pos hg, hv]
        exact hE
      rw [hemb]
      rfl
    · rw [if_neg hg]
      rw [if_neg hg] at hE
      obtain rfl := Option.some.inj hE
      rfl
  · simpa using hn
  · intro c hc
    have h3 : (cP ++ cE).all (fun c => (wsClaimShape Q.P.wsLay c).isOk) = true := by
      simpa using hs
    exact List.all_eq_true.1 h3 c hc

/-- CONDITIONAL on every hypothesis named. **THE MERGE's JOB IS MADE AND HAS ITS CALL's PUBLIC
SHAPE.** -/
theorem merge_fit (hB : claimsB Q.P Q.hp Q.g = true) (hv : envOf Q p = some v)
    (hz : zkFits Q.P p.fo.zk = true) (ht : k4TokensFit Q w.tokv = true)
    (hrs : p.rs.size = Q.hp.lamS) (hrt : p.rt.size = Q.P.y.h.lt)
    (hZ : p.ZE.size = (if (Q.g == 0) = true then Q.P.y.ls + Q.P.y.h.lt else 0))
    (hk : p.tkh.size = (if (Q.g == 0) = true then Q.P.y.lPd - Q.P.y.ls else 0)) :
    ∃ j, jobMerge Q w p = some j ∧ k4JobFits ((k4Shapes Q).getD 6 ⟨0, [], none⟩) j = true := by
  obtain ⟨cls, hc, _, _⟩ := merge_claims_fit (w := w) hB hv hz ht hrs hrt hZ hk
  refine ⟨mergeJobOf Q.P.wsLay w.w cls p.rhoW, ?_, ?_⟩
  · unfold jobMerge
    rw [hc]
    rfl
  · rw [k4Shapes_merge]
    exact mergeJob_jobFits _ _ _ _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.merge_claims_fit
#print axioms ProofFile.Honest.K4.merge_fit
