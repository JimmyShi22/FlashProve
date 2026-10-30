-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumAtRun2.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. Under the test `k4Fits`, the makers of the second token sumcheck's job and of the
batched sumcheck's job return at the run and their jobs fit their calls: the two that SumAtRun.lean
leaves out.

  `makersAt_any`   the clause on the makers at the run, at every list of shown values
  `at_terms`, `at_stack`   two clauses of it
  `terms_run`, `stack_run`   **the two makers at the run**

Limits. The premises are SumAtRun.lean's: the test `k4Fits` at the input's tokens; the challenges
heard so far have the shapes of the sub-protocol's rounds and end just in front of the sumcheck;
what the input's reader of the lookup returns has the lengths of what the test was asked at. On
returns and public shapes alone: nothing on what a job sums.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Forest.Heard)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw
open OnBytes.Desc.First.K4.RtPub (any_some)

/-- The clause on the makers at the run, at every list of shown values. -/
theorem makersAt_any {Q : K4Pub} {fo : Forest.Heard} (w : K4In)
    (hk : k4Fits Q fo w.tokv = true) (k : ℕ) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD k 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) (sh : Array E) :
    ∃ s : ℕ → Pts, s k = ptsOf Q w heard ∧ k4MakersAt Q w (k4AtBat Q fo) s sh = true := by
  obtain ⟨s, hs, h⟩ := makersAt_one w hk k heard hf hn hL
  refine ⟨s, hs, ?_⟩
  rw [k4MakersAt_skel Q (w₀ := w) ⟨fun _ => rfl, fun _ => rfl⟩ (lookSkel_refl _)
    (fun i => ptsFull_refl (s i)) sh (Array.replicate (nEndT Q.P.y) zeroE)]
  exact h

/-- The clause on the second token sumcheck. -/
theorem at_terms {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    (jobTerms Q w (s 2)).any (k4JobFits ((k4Shapes Q).getD 2 ⟨0, [], none⟩)) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- The clause on the batched sumcheck. -/
theorem at_stack {Q : K4Pub} {w : K4In} {b s : ℕ → Pts} {sh : Array E}
    (h : k4MakersAt Q w b s sh = true) :
    (jobStack Q w (s 3) sh).any (k4JobFits ((k4Shapes Q).getD 3 ⟨0, [], none⟩)) = true := by
  unfold k4MakersAt at h
  simp only [Bool.and_eq_true] at h
  repeat (first | (with_reducible exact h.2) | replace h := h.1)

/-- **The second token sumcheck: what the two jobs share is made at the run, the job is made of it,
and it fits its call.** -/
theorem terms_run {Q : K4Pub} {fo : Forest.Heard} (w : K4In) (hk : k4Fits Q fo w.tokv = true)
    (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD 2 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) :
    ∃ S J, OnBytes.Desc.First.K4.Honest.Sides.of Q w (ptsOf Q w heard) = some S ∧
      jobTermsOn S = some J ∧ k4JobFits ((k4Shapes Q).getD 2 ⟨0, [], none⟩) J = true := by
  obtain ⟨s, hs, h⟩ := makersAt_one w hk 2 heard hf hn hL
  have h' := at_terms h
  rw [hs] at h'
  obtain ⟨J, hj, hfit⟩ := any_some h'
  unfold jobTerms at hj
  obtain ⟨S, hS, hJ⟩ := Option.bind_eq_some_iff.mp hj
  exact ⟨S, J, hS, hJ, hfit⟩

/-- **The batched sumcheck: the job's data are made at the run, at every list of shown values, and
the job fits its call.** -/
theorem stack_run {Q : K4Pub} {fo : Forest.Heard} (w : K4In) (hk : k4Fits Q fo w.tokv = true)
    (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (heard.drop Q.r0).length = (starts Q).getD 3 0)
    (hL : LookSkel (w.look (heard.take Q.r0)) fo) (sh : Array E) :
    ∃ D, stackData Q w (ptsOf Q w heard) sh = some D ∧
      k4JobFits ((k4Shapes Q).getD 3 ⟨0, [], none⟩) (jobStackOn D) = true := by
  obtain ⟨s, hs, h⟩ := makersAt_any w hk 3 heard hf hn hL sh
  have h' := at_stack h
  rw [hs] at h'
  obtain ⟨J, hj, hfit⟩ := any_some h'
  unfold jobStack at hj
  obtain ⟨D, hD, rfl⟩ := Option.map_eq_some_iff.mp hj
  exact ⟨D, hD, hfit⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.makersAt_any
#print axioms ProofFile.Honest.K4.at_terms
#print axioms ProofFile.Honest.K4.at_stack
#print axioms ProofFile.Honest.K4.terms_run
#print axioms ProofFile.Honest.K4.stack_run
