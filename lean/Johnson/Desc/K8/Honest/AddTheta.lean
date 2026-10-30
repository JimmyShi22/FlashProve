-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/AddTheta.lean: THE ADDING OF A LIST OF CLAIMS TO THE LEDGER (`K9.addList`,
Johnson/Desc/First/Batch/Add.lean) LEAVES THE LEDGER's BATCHING ELEMENT. For the smallness test's
tests behind the adding: with Johnson/Desc/K8/Honest/ThetaRests.lean: the adding stands between the
gatherer's runs and these tests. Lemmas on the verifier's own text; none of the library's goals.

  `addForm_theta`, `addRuns_theta`, `addOne_theta`   each step of one adding leaves it
  **`addList_theta`**   addList F cls = .ok G → G.theta = F.theta
Limits. From a yes of the adding alone. Nothing on the sums that the adding turns.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Batch.Law.AddAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K9 (addList addOne addForm addRuns addEntry addSlot addRun weightNext)

/-- The adding of a form leaves the batching element. -/
theorem addForm_theta {F G : Fork} {w : E} {a : Aff} (h : addForm F w a = .ok G) :
    G.theta = F.theta := by
  unfold addForm at h
  simp only [] at h
  cases h1 : a.ents.foldlM (addEntry w) F.trees with
  | error m => simp only [bind, Except.bind, h1] at h; exact nomatch h
  | ok T =>
    cases h2 : a.slots.foldlM (addSlot w F.ns) F.LS with
    | error m => simp only [bind, Except.bind, h1, h2] at h; exact nomatch h
    | ok L' =>
      simp only [bind, Except.bind, h1, h2, pure, Except.pure] at h
      rw [← Except.ok.inj h]

/-- The adding of runs leaves the batching element. -/
theorem addRuns_theta {F G : Fork} {w : E} {runs : Array Run2} (h : addRuns F w runs = .ok G) :
    G.theta = F.theta := by
  unfold addRuns at h
  simp only [] at h
  cases h1 : runs.foldlM (addRun w) F.trees with
  | error m => simp only [bind, Except.bind, h1] at h; exact nomatch h
  | ok T =>
    simp only [bind, Except.bind, h1, pure, Except.pure] at h
    rw [← Except.ok.inj h]

/-- The adding of one claim leaves the batching element. -/
theorem addOne_theta {F G : Fork} {cl : Claim} (h : addOne F cl = .ok G) : G.theta = F.theta := by
  unfold addOne at h
  simp only [] at h
  cases hx : weightNext F with
  | error m => rw [hx] at h; exact nomatch h
  | ok x =>
    rw [hx] at h
    have ex : x.2 = { F with kapMapF := F.kapMapF.set! F.nClaim true, nClaim := F.nClaim + 1 } :=
      congrArg (·.2) (VerifiableInference.Desc.K9L.weightNext_ok F x hx).2.2.2.2.2
    have t1 : x.2.theta = F.theta := by rw [ex]
    cases hf : addForm x.2 ((cl.eqFirst.map fun first =>
        powE F.theta (F.planClaimsF + first)).getD x.1) cl.form with
    | error m => simp only [bind, Except.bind, hf] at h; exact nomatch h
    | ok H =>
      simp only [bind, Except.bind, hf] at h
      exact (addRuns_theta h).trans ((addForm_theta hf).trans t1)

/-- **The adding of a list of claims leaves the batching element.** -/
theorem addList_theta : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    G.theta = F.theta
  | [], F, G, h => by
    have e : F = G := Except.ok.inj h
    rw [e]
  | cl :: l, F, G, h => by
    unfold addList at h
    rw [List.foldlM_cons] at h
    cases hH : addOne F cl with
    | error m => rw [hH] at h; exact nomatch h
    | ok H =>
      rw [hH] at h
      exact (addList_theta l H G h).trans (addOne_theta hH)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.addForm_theta
#print axioms VerifiableInference.Desc.First.K8.Honest.addRuns_theta
#print axioms VerifiableInference.Desc.First.K8.Honest.addOne_theta
#print axioms VerifiableInference.Desc.First.K8.Honest.addList_theta
