-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/PlanListsProof.lean: from a yes of `configure`, the plans of a proof's three chains
against their lists.

The like of `configure_key_is` (OnBytes/Plan/PlanListsConfigure.lean) for a proof. If `configure`
(OnBytes/Params/Configure.lean) says yes, the three plans that it returns for a proof are finished
plans that hold, each with the rounds of a list of descriptions: the first chain's list is
`Plan.firstChainList` (OnBytes/Plan/PlanListsReq.lean), under a request's own scope; the shared
chain's and the second chain's are those of OnBytes/Params/PlanListsChains.lean, under the scopes
`.shared` and `.request`, since a proof's test on the table is no one-time test. All three are under
the setting that follows from the lines. The sub-proofs' lists are given, under the hypothesis
`Plan.SubRuns`; OnBytes/Model/LinkRoundsList.lean discharges it for the
model's sub-proofs.

Main theorems: `sized_proof`, `proofSized_set`, `configure_proofPlans`, `configure_proof_sizes`,
`configure_proof_is`.
What is not claimed: that `configure` says yes. What OnBytes/Plan/PlanListsReq.lean and
OnBytes/Params/PlanListsChains.lean do not claim is not claimed here. Of what `configure` tests
besides the plans (the conditions of OnBytes/Params/Gate.lean, the shapes' fit, the caller's bits)
nothing is kept here. Less is kept than in `configure_key_is`: not that the second chain's test has
two stages (`secondPlan_is` has it), not what the sizes Ls hold (`linSizeOf_lines` and
`proofSized_set` give it), not that a sending's number of trees was there. Nothing on the three
chains' parameter bytes. No bound on a cheating prover's chance follows from this file alone. For
proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Plan.PlanListsConfigure
import OnBytes.Plan.PlanListsReq

set_option autoImplicit false

namespace OnBytes.Params

/-- What `sized` returns holds the proof's sizes that `proofSized` makes. -/
theorem sized_proof {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    proofSized l x.sub = some z.proof := by
  unfold sized at h
  extract_lets at h
  replace h := exc_guard h
  obtain ⟨proof, hp, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨key, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨⟨link, codes⟩, _, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  exact orRefuse_ok hp

/-- A proof's sizes have the lines' setting, and their test on the table is no one-time test. -/
theorem proofSized_set {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) : z.set = settingOf l ∧ z.batch.lines.oneTime = false := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, _, h⟩ := opt_bind h
  obtain ⟨stages, _, h⟩ := opt_bind h
  obtain ⟨T, _, h⟩ := opt_bind h
  split at h
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, hb, h⟩ := opt_bind h
  cases h
  refine ⟨rfl, ?_⟩
  show batch.lines.oneTime = false
  rw [linSized_lines hb]
  rfl

/-- What `configure` returns: the proof's three plans are what the three routines returned on the
proof's sizes. -/
theorem configure_proofPlans {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    ∃ F S2 S3, made.proof = [F, S2, S3] ∧ firstPlan made.sized.proof x.sub = .ok F ∧
      sharedPlan made.sized.proof.set made.sized.proof.codes made.sized.proof.batch = .ok S2 ∧
      secondPlan made.sized.proof.set made.sized.proof.batch = .ok S3 := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, hp, h⟩ := exc_bind h
  obtain ⟨P1, h1, h⟩ := exc_bind h
  obtain ⟨P2, h2, h⟩ := exc_bind h
  obtain ⟨P3, h3, h⟩ := exc_bind h
  obtain ⟨entry, he, h⟩ := exc_bind h
  unfold proofPlans at hp
  obtain ⟨F, hF, hp⟩ := exc_bind hp
  obtain ⟨S2, hS2, hp⟩ := exc_bind hp
  obtain ⟨S3, hS3, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨_, _, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  exact ⟨F, S2, S3, rfl, hF, hS2, hS3⟩

/-- From `configure`'s yes: the proof's sizes are `proofSized`'s, their setting is the lines', and
their test on the table is no one-time test. The first chain's list reads the setting from the
sizes: by the second part it is the setting of `PlanIs`. -/
theorem configure_proof_sizes {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    proofSized l x.sub = some made.sized.proof ∧ made.sized.proof.set = settingOf l ∧
      made.sized.proof.batch.lines.oneTime = false :=
  ⟨sized_proof (configure_plans h).1, proofSized_set (sized_proof (configure_plans h).1)⟩

/-- **From `configure`'s yes: the plans of a proof's three chains against their lists**, all under
the lines' setting: the first chain under a request's own scope, against the frame's list with the
sub-proofs' lists `L` and `after` between; the shared chain under the scope `.shared`; the second
chain under a request's own scope. Ls: the sizes that the plans of the test on the table read.
Asked: the sub-proofs' routines add the rounds of these lists (`Plan.SubRuns`). Kept besides: the
sizes are `proofSized`'s; their setting, which the first chain's list reads, is the lines'; the
number of columns is the one in the shape. -/
theorem configure_proof_is {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made)
    {L : Nat → Nat → List RoundSpec} {after : List RoundSpec}
    (S : Plan.SubRuns (settingOf l) x.sub L after) :
    proofSized l x.sub = some made.sized.proof ∧ made.sized.proof.set = settingOf l ∧
      ∃ F S2 S3 Ls, made.proof = [F, S2, S3] ∧
      linSizeOf made.sized.proof.codes made.sized.proof.batch = some Ls ∧
      linColumns (settingOf l) .shared made.sized.proof.batch.table Ls =
        made.sized.proof.batch.shape.fold.columns ∧
      PlanIs F (settingOf l) .request (Plan.firstChainList made.sized.proof x.sub L after) ∧
      PlanIs S2 (settingOf l) .shared
        (linSharedTests (settingOf l) .shared made.sized.proof.batch Ls ++ [sealRound]) ∧
      PlanIs S3 (settingOf l) .request
        (secondChainList (settingOf l) .request made.sized.proof.batch) := by
  have hp := sized_proof (configure_plans h).1
  obtain ⟨hset, hot⟩ := proofSized_set hp
  obtain ⟨F, S2, S3, hl, hF, hS2, hS3⟩ := configure_proofPlans h
  rw [hset] at hS2 hS3
  obtain ⟨Ls, hLs, hcol, p2⟩ := sharedPlan_is hS2
  have p3 := secondPlan_rounds hS3
  rw [hot] at hcol p2 p3
  have p1 := Plan.firstPlan_rounds (z := made.sized.proof) (by rw [hset]; exact S) hF
  rw [hset] at p1
  exact ⟨hp, hset, F, S2, S3, Ls, hl, hLs, hcol, p1, p2, p3⟩

end OnBytes.Params

#print axioms OnBytes.Params.sized_proof
#print axioms OnBytes.Params.proofSized_set
#print axioms OnBytes.Params.configure_proofPlans
#print axioms OnBytes.Params.configure_proof_sizes
#print axioms OnBytes.Params.configure_proof_is
