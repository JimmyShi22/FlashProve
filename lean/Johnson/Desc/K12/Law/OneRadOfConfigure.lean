-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OneRadOfConfigure.lean: `OneRad` (OneRadOfPlan.lean) at the four proximity
tests of a proof file, from the yes of the planner's `configure`.

It pays the two premises of OneRadConfigured.lean.
Main names:
  `said_proofSized`: every stage of the four tests has a group that the sizing returned (`MSaid`,
    SaidOfSizing.lean), over `proofSized_parts` and `linSized_parts`
    (OnBytes/Params/Fit/), which name the makers' calls.
  `holds_of_finishHeld`, `proof_holds`: the three plans of a proof file have passed `Planned.holds`:
    the routine that finishes a plan returns it only then.
  `oneRad_folded_cfg`, `oneRad_own_cfg`: from `configure`'s yes, no other premise.
    `oneRad_omega_cfg`: besides, the shape says that the shared chain splits. `oneRad_last_cfg`:
    besides, `Plan.SubRuns`.
Limits: as OneRadOfPlan.lean's. The proof file's four tests only. Nothing on soundness. Nothing on
hiding.

-/
import OnBytes.Params.Fit.SizedParts
import Johnson.Desc.K12.Law.OneRadConfigured
import Johnson.Desc.K12.Law.SaidOfSizing

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice

/-- Every stage of a proof's four proximity tests has a group that the sizing returned by
`sizeGroup`. -/
theorem said_proofSized {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    (∀ y ∈ z.last.stages, MSaid y.g) ∧ (∀ y ∈ z.batch.folded.stages, MSaid y.g) ∧
      (∀ y ∈ z.batch.omega.stages, MSaid y.g) ∧ ∀ y ∈ z.batch.own.stages, MSaid y.g := by
  obtain ⟨load, shape, K, T, codes1, _, _, hl, hg, hs, _, _, hb⟩ := proofSized_parts h
  obtain ⟨G, X, Y, Z, a, b, stU, stO, stW, _, _, _, hT, hU, hO, hW, eU, eO, eW, _⟩ :=
    linSized_parts hb
  have sT := said_linTurns 33 {} {} {} (X, Y, Z) (Or.inl rfl) hT
  have sL : MSaid z.link.group := said_groupFrom 32 0 z.link hl
  have sLast : MSaid z.last.group := by
    rw [hg]
    exact sL
  refine ⟨said_stages sLast hs, ?_, ?_, ?_⟩
  · rw [eU]
    exact said_stages sT.1 hU
  · rw [eO]
    rcases hO with ⟨_, hO⟩ | rfl
    · exact said_stages sT.2.1 hO
    · intro y hy
      cases hy
  · rw [eW]
    exact said_stages sT.2.2 hW

theorem holds_of_finishHeld {s : Setting} {c : Scope} {x : Planning Unit} {P : Planned}
    (h : finishHeld s c x = .ok P) : P.holds = true := by
  unfold finishHeld at h
  obtain ⟨p, _, h⟩ := exc_bind h
  split at h
  · rename_i hp
    cases h
    exact hp
  · cases h

section
variable {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {M : Configured}
  (h : configure l x cfg bits = .ok M)
include h

/-- The three plans of a proof that `configure` returns have passed the plan's verdict. -/
theorem proof_holds : ∀ P ∈ M.proof, P.holds = true := by
  obtain ⟨F, S2, S3, hl, hF, hS2, hS3⟩ := configure_proofPlans h
  intro P hP
  rw [hl] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact holds_of_finishHeld hF
  · exact holds_of_finishHeld hS2
  · exact holds_of_finishHeld hS3

/-- **From `configure`'s yes alone**: the folded row's test. -/
theorem oneRad_folded_cfg (σ : Setting) : OneRad σ M.sized.proof.batch.folded.stages :=
  oneRad_folded h (proof_holds h) σ (said_proofSized (configure_proof_sizes h).1).2.1

/-- Omega's test, where the shared chain has one. -/
theorem oneRad_omega_cfg (hs : M.sized.proof.batch.shape.sharedSplitNeeded = true) (σ : Setting) :
    OneRad σ M.sized.proof.batch.omega.stages :=
  oneRad_omega h (proof_holds h) σ hs (said_proofSized (configure_proof_sizes h).1).2.2.1

/-- The own test. -/
theorem oneRad_own_cfg (σ : Setting) : OneRad σ M.sized.proof.batch.own.stages :=
  oneRad_own h (proof_holds h) σ (said_proofSized (configure_proof_sizes h).1).2.2.2

/-- The first chain's last test: asked besides: `Plan.SubRuns`. -/
theorem oneRad_last_cfg {L : Nat → Nat → List RoundSpec} {after : List RoundSpec}
    (S : Plan.SubRuns (settingOf l) x.sub L after) (σ : Setting) :
    OneRad σ M.sized.proof.last.stages :=
  oneRad_last h (proof_holds h) σ S (said_proofSized (configure_proof_sizes h).1).1

end

end H2K.Pub

#print axioms H2K.Pub.oneRad_last_cfg
#print axioms H2K.Pub.said_proofSized
#print axioms H2K.Pub.proof_holds
#print axioms H2K.Pub.oneRad_folded_cfg
#print axioms H2K.Pub.oneRad_omega_cfg
#print axioms H2K.Pub.oneRad_own_cfg
