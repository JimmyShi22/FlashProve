-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/PlacesNums.lean: what `H2U.placesOfMade`
(Johnson/Desc/K12/Plan/PlaceOfPlan.lean) lays as the stages and the bits of work of a proof file's
four places of a proximity test (the kind K12), and that a place at which the block's test on the
plan says yes has these numbers. Statements and proofs.

Main names:
  `mk_stages`: `mkPlace` lays `st.map stageNums` and its argument `work`.
  `workShared A`, `workOwn A`: the setting's bits of work for a round of positions, at the scope of
    the two tests on the shared chain, and of the own test.
  `later_nums`: the three places of `placesLater`: the stages are those of the sized batch record's
    `folded`, `omega` and `own`.
  `places_nums`: the four places of `placesOfMade m`, off `m.p.chains.made.sized`.
  `nums_of_planOk`: where the test on the plan of `proximityTestKind guardedProximityTestParts (proximityTestParametersAt place x)` says yes,
    `(proximityTestParametersAt place x).nums = x.nums`: the place is not `noP12`.
Limits: Mathlib stands beneath, through the closure of Johnson/Desc/K12/AtPlan.lean. By unfolding
the makers' texts alone: nothing on the planner, on a plan's entries or on what a description seats.
Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Params Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2U (placesOfMade placesLater laterOfProof mkPlace stageNums Places4 PlaceNums Later3 LaterArgs
  proximityTestParametersAt noP12)

theorem mk_stages (answers chain : Nat) (st : List StageSize) (rows work : Nat) (own : Bool)
    (t : H2U.TestCut) (fa : H2U.FirstAt) (g0 : Nat) (early : Bool) :
    (mkPlace answers chain st rows work own t fa g0 early).nums.stages = st.map stageNums ∧
      (mkPlace answers chain st rows work own t fa g0 early).nums.work = work := ⟨rfl, rfl⟩

/-- The work of the two tests on the shared chain, and of the own test. -/
def workShared (A : LaterArgs) : Nat :=
  A.set.workOf .query (if A.batch.lines.oneTime then .once else .shared)

def workOwn (A : LaterArgs) : Nat :=
  A.set.workOf .query (if A.batch.lines.oneTime then .once else .request)

theorem later_nums (A : LaterArgs) (X : Later3) (h : placesLater A = .ok X) :
    (X.U.nums.stages = A.batch.folded.stages.map stageNums ∧ X.U.nums.work = workShared A) ∧
    (∀ o, X.O = some o →
      o.nums.stages = A.batch.omega.stages.map stageNums ∧ o.nums.work = workShared A) ∧
    (X.W.nums.stages = A.batch.own.stages.map stageNums ∧ X.W.nums.work = workOwn A) := by
  unfold placesLater at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h
       refine ⟨⟨rfl, ?_⟩, ?_, ⟨rfl, ?_⟩⟩
       · simp [workShared, mkPlace, *]
       · intro o ho
         cases ho
         exact ⟨rfl, by simp [workShared, mkPlace, *]⟩
       · simp [workOwn, mkPlace, *])
    | (cases h
       refine ⟨⟨rfl, ?_⟩, ?_, ⟨rfl, ?_⟩⟩
       · simp [workShared, mkPlace, *]
       · intro o ho
         cases ho
       · simp [workOwn, mkPlace, *])
    | cases h

/-- **What `placesOfMade` lays as stages and as bits of work**, off the planner's sized records and
its
setting. -/
theorem places_nums (m : Made) (X : Places4) (h : placesOfMade m = .ok X) :
    (X.L.nums.stages = m.p.chains.made.sized.proof.last.stages.map stageNums ∧
      X.L.nums.work = m.p.chains.made.sized.set.workOf .query .request) ∧
    ∃ g, (X.U.nums.stages = m.p.chains.made.sized.proof.batch.folded.stages.map stageNums ∧
        X.U.nums.work = workShared (laterOfProof m g)) ∧
      (∀ o, X.O = some o →
        o.nums.stages = m.p.chains.made.sized.proof.batch.omega.stages.map stageNums ∧
          o.nums.work = workShared (laterOfProof m g)) ∧
      (X.W.nums.stages = m.p.chains.made.sized.proof.batch.own.stages.map stageNums ∧
        X.W.nums.work = workOwn (laterOfProof m g)) := by
  unfold placesOfMade at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i X3 hX3
        split at h
        · cases h
        · cases h
          exact ⟨⟨rfl, rfl⟩, _, later_nums _ X3 hX3⟩

/-- A place at which the block's test on the plan says yes has the numbers that it was made of. -/
theorem nums_of_planOk {Cl : Type} (place : Place) (x : PlaceNums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place x) : Block T12 Cl).planOk = true) :
    (proximityTestParametersAt place x).nums = x.nums := by
  unfold proximityTestParametersAt at hp ⊢
  split
  · rename_i hc
    rw [if_pos hc] at hp
    exact absurd hp (by simp [proximityTestKind, noP12])
  · rename_i hc
    rw [if_neg hc] at hp
    split
    · rfl
    · rename_i ho
      rw [ho] at hp
      exact absurd hp (by simp [proximityTestKind, noP12])

end H2K.Made

#print axioms H2K.Made.places_nums
#print axioms H2K.Made.nums_of_planOk
