-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OneRadConfigured.lean: `OneRad` (OneRadOfPlan.lean) at the four proximity tests
of a proof file, at what the planner's `configure` returns, under two premises.

The laws on `configure` say which list of rounds each of a proof file's three plans has
(OnBytes/Plan/PlanListsProof.lean). This file shows that each test's stages stand in its chain's
list, and calls `oneRad_of_oneDistance`.
Main names:
  `oneDistance_of_holds`: a plan that has passed `Planned.holds` has passed `oneDistance`.
  `groups_len`, `mem_reqListFrom`: the last test's stages stand in the first chain's list, behind
    the last link.
  `oneRad_last`, `oneRad_folded`, `oneRad_omega`, `oneRad_own`: the four tests. Asked: the three
    plans have passed `Planned.holds`; every stage's group has the rule johnson or named, or m = 0.
    At the last test besides: the sub-proofs' routines add the rounds of given lists
    (`Plan.SubRuns`). At Omega's test besides: the shape says that the shared chain splits; else
    that chain's list has no such test.
OneRadOfConfigure.lean pays the two premises.
Limits: as OneRadOfPlan.lean's. The proof file's four tests only: not the key file's, not the entry
file's. Nothing on soundness. Nothing on hiding.

-/
import OnBytes.Plan.PlanListsProof
import Johnson.Desc.K12.Law.OneRadOfPlan

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice

theorem oneDistance_of_holds {P : Planned} (h : P.holds = true) : P.oneDistance = true := by
  unfold Planned.holds at h
  exact (Bool.and_eq_true_iff.1 h).2

theorem groupsFrom_len (s : ReqShape) : ∀ (count l : Nat) (alive : List ReqAlive),
    (reqGroupsFrom s count l alive).length = count
  | 0, _, _ => rfl
  | count + 1, l, alive => by
    show (reqGroupsFrom s count (l + 1) (reqGroupAt s l alive).2).length + 1 = count + 1
    rw [groupsFrom_len s count]

theorem groups_len (s : ReqShape) : (reqGroups s).toList.length = s.link.length + 1 := by
  rw [reqGroups_eq, groupsFrom_len]

/-- The last test's stages stand in the frame's list of a chain of links: behind the last link. -/
theorem mem_reqListFrom (z : ProofSized) (L : Nat → Nat → List RoundSpec) :
    ∀ (links : List ReqLink) (gs : List ReqGroup) (n : Nat) (open_ : List Nat) (before : GroupSize),
      gs.length = links.length + 1 →
      ∀ y ∈ stagesList z.set .request 0 z.request.choice.masksRide true z.last.stages,
        y ∈ Plan.reqListFrom z L n gs links open_ before
  | [], [], _, _, _, hg, _, _ => by cases hg
  | [], g :: gs, n, open_, before, _, y, hy => by
    unfold Plan.reqListFrom
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
  | k :: ks, [], _, _, _, hg, _, _ => by cases hg
  | k :: ks, g :: gs, n, open_, before, hg, y, hy => by
    have ih := mem_reqListFrom z L ks gs (n + 1) (open_.drop 1) (Plan.closedGroup z g gs)
      (by simpa using hg) y hy
    unfold Plan.reqListFrom
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ ih)))))

section
variable {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {M : Configured}
  (h : configure l x cfg bits = .ok M) (hh : ∀ P ∈ M.proof, P.holds = true) (σ : Setting)
include h hh

/-- The folded row's test. -/
theorem oneRad_folded
    (hj : ∀ y ∈ M.sized.proof.batch.folded.stages,
      y.g.rule = .johnson ∨ y.g.rule = .named ∨ y.g.m = 0) :
    OneRad σ M.sized.proof.batch.folded.stages := by
  obtain ⟨F, S2, S3, hl, _, hS2, _⟩ := configure_proofPlans h
  obtain ⟨Ls, _, _, p2⟩ := sharedPlan_is hS2
  refine oneRad_of_oneDistance p2.rounds
    (oneDistance_of_holds (hh S2 (by rw [hl]; simp))) _
    (if M.sized.proof.batch.shape.masksAhead then 0 else 1)
    M.sized.proof.batch.shape.choice.masksRide ?_ hj σ
  intro y hy
  refine List.mem_append_left _ ?_
  unfold linSharedTests
  refine List.mem_append_right _ ?_
  split
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _ hy))
  · exact List.mem_cons_of_mem _ hy

/-- Omega's test, where the shared chain has one. -/
theorem oneRad_omega (hs : M.sized.proof.batch.shape.sharedSplitNeeded = true)
    (hj : ∀ y ∈ M.sized.proof.batch.omega.stages,
      y.g.rule = .johnson ∨ y.g.rule = .named ∨ y.g.m = 0) :
    OneRad σ M.sized.proof.batch.omega.stages := by
  obtain ⟨F, S2, S3, hl, _, hS2, _⟩ := configure_proofPlans h
  obtain ⟨Ls, _, _, p2⟩ := sharedPlan_is hS2
  refine oneRad_of_oneDistance p2.rounds
    (oneDistance_of_holds (hh S2 (by rw [hl]; simp))) _ 1
    M.sized.proof.batch.shape.choice.masksRide ?_ hj σ
  intro y hy
  refine List.mem_append_left _ ?_
  unfold linSharedTests
  refine List.mem_append_right _ ?_
  rw [if_pos hs]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hy))

/-- The own test. -/
theorem oneRad_own
    (hj : ∀ y ∈ M.sized.proof.batch.own.stages,
      y.g.rule = .johnson ∨ y.g.rule = .named ∨ y.g.m = 0) :
    OneRad σ M.sized.proof.batch.own.stages := by
  obtain ⟨F, S2, S3, hl, _, _, hS3⟩ := configure_proofPlans h
  have p3 := secondPlan_rounds hS3
  exact oneRad_of_oneDistance p3.rounds
    (oneDistance_of_holds (hh S3 (by rw [hl]; simp))) _
    (if M.sized.proof.batch.shape.masksAhead then 0 else 1)
    M.sized.proof.batch.shape.choice.masksRide (fun y hy => List.mem_cons_of_mem _ hy) hj σ

/-- The first chain's last test. Asked besides: the sub-proofs' routines add the rounds of given
lists (`Plan.SubRuns`). -/
theorem oneRad_last {L : Nat → Nat → List RoundSpec} {after : List RoundSpec}
    (S : Plan.SubRuns (settingOf l) x.sub L after)
    (hj : ∀ y ∈ M.sized.proof.last.stages, y.g.rule = .johnson ∨ y.g.rule = .named ∨ y.g.m = 0) :
    OneRad σ M.sized.proof.last.stages := by
  obtain ⟨F, S2, S3, hl, hF, _, _⟩ := configure_proofPlans h
  have hset := (configure_proof_sizes h).2.1
  have p1 := Plan.firstPlan_rounds (z := M.sized.proof) (by rw [hset]; exact S) hF
  refine oneRad_of_oneDistance p1.rounds
    (oneDistance_of_holds (hh F (by rw [hl]; simp))) _ 0
    M.sized.proof.request.choice.masksRide ?_ hj σ
  intro y hy
  unfold Plan.firstChainList
  exact List.mem_append_left _ (mem_reqListFrom M.sized.proof L _ _ 0 _ _
    (groups_len M.sized.proof.request) y hy)

end

end H2K.Pub

#print axioms H2K.Pub.oneRad_last
#print axioms H2K.Pub.oneRad_folded
#print axioms H2K.Pub.oneRad_omega
#print axioms H2K.Pub.oneRad_own
