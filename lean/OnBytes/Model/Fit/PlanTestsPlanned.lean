-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/PlanTestsPlanned.lean: from the program's yes on the three configuration files:
the planner's yes and the two readers' answers; and a first form of "the first chain of the key and
of the proof has two rounds at least, and the last round of the first and of the shared chain asks
for no work", where the made plans fit the format's words.

Verify.planned (OnBytes/Model/Verify.lean) calls chainsOf (OnBytes/Model/VerifyChains.lean), which
calls the planner and reads the chains back from the planner's own parameter bytes.
OnBytes/Params/Fit/PlanTestsMade.lean says the two things of the plans as made.
OnBytes/Model/ReadBackMade.lean says that the plans as read back are the plans as made, where the
made plans fit the format's words (Fmt.Plan.fit). This file lays the two together.

Main theorems.
 - chainsOf_reads, planned_made: from the program's yes: the planner's yes at the made record, and
   the two readers' answers. These two are what the files above this one use.
 - planTests_planned: the six clauses at the chains of what Verify.planned returns. It is overtaken
   by planTests_planned_norm (OnBytes/Model/Fit/ReadNormMade.lean), which asks less.

What is not claimed: that the made plans fit (hf): a premise. In chainsOf_reads and planned_made
the lines l and the shapes x stand under "there are" and are tied to nothing: that they are the
lines of p.X and what shapesOf returns is said in OnBytes/Model/Fit/PlannedParts.lean. Nothing on
the dry runs. Nothing on soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Model.ReadBackMade
import OnBytes.Model.Verify
import OnBytes.Params.Fit.PlanTestsMade

set_option autoImplicit false

namespace OnBytes.Model.Verify

open OnBytes.Params

/-- From chainsOf's yes: the planner's yes, and the readers' answers on its bytes. -/
theorem chainsOf_reads {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X lay c = .ok ch) :
    ∃ (l : Lines) (x : Shapes), configure l x c 0 = .ok ch.made ∧
      KeyChains.read ch.made.keyOneTime ch.made.keyShared ch.made.keySecond = some ch.key ∧
      ProofChains.read ch.made.first ch.made.shared ch.made.second = some ch.proof := by
  unfold chainsOf at h
  obtain ⟨⟨links, shapes⟩, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨z, _, h⟩ := exc_bind h
  obtain ⟨u, _, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  split at h
  · rename_i key link proof hK hL hP
    cases h
    exact ⟨X.P.frame, shapes, hm, hK, hP⟩
  · cases h

/-- The same from Verify.planned's yes. -/
theorem planned_made {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) :
    ∃ (l : Lines) (x : Shapes), configure l x p.cfg 0 = .ok p.chains.made ∧
      KeyChains.read p.chains.made.keyOneTime p.chains.made.keyShared p.chains.made.keySecond =
        some p.chains.key ∧
      ProofChains.read p.chains.made.first p.chains.made.shared p.chains.made.second =
        some p.chains.proof := by
  unfold planned at h
  obtain ⟨X, _, h⟩ := exc_bind h
  obtain ⟨ch, hc, h⟩ := exc_bind h
  obtain ⟨b, _, h⟩ := exc_bind h
  cases h
  exact chainsOf_reads hc

/-- **From the program's yes on the three configuration files**, where the made plans fit. -/
theorem planTests_planned {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p)
    (hf : ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, P.plan.fit = true) :
    (2 ≤ p.chains.key.oneTime.given.rounds.length ∧
        EndsSeal p.chains.key.oneTime.given.rounds ∧
        EndsSeal p.chains.key.shared.given.rounds) ∧
      (2 ≤ p.chains.proof.first.given.rounds.length ∧
        EndsSeal p.chains.proof.first.given.rounds ∧
        EndsSeal p.chains.proof.shared.given.rounds) := by
  obtain ⟨l, x, hm, hK, hP⟩ := planned_made h
  obtain ⟨_, _, K1, K2, K3, ek, _⟩ := configure_plans hm
  obtain ⟨F, S2, S3, ep, _⟩ := configure_proofPlans hm
  obtain ⟨a1, a2, _⟩ := key_read_made hm hK
    (fun P hPm => hf P (List.mem_append_left _ hPm)) ek
  obtain ⟨b1, b2, _⟩ := proof_read_made hm hP
    (fun P hPm => hf P (List.mem_append_right _ hPm)) ep
  have t := planTests_made hm ek ep
  unfold Given.rounds
  rw [a1, a2, b1, b2]
  exact t

end OnBytes.Model.Verify
