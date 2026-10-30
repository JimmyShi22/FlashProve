-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/PlanPlaysAt.lean: WHAT "THE MEMBER PLAYS" ASKS OF THE PLAN
(`PlanPlays`, PlaysK12.lean in this folder) AS ONE TEST WITH CODE, with its law; and that test is
true, BY THE KERNEL's OWN EVALUATION (`decide +kernel`), at two small synthetic places and at the
written place of the key file's test on the ranges at the full size (`piKRFull`,
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean). The test reads of a job its place and whether the
first fold sends its own table: nothing else. Definitions with code, statements and proofs, and
evaluations (#guard).

  `bare`         a job with a place and that one word, and nothing else in it
  `tablesFitB_congr`, `newWideB_congr`   the two tests read of a job these two things alone
  `planPlaysB`   the six clauses, of the place, that word and the number of trees sent in front
  `planPlays_of_B`   its "true" gives `PlanPlays` at every job with that place and that word
  **`planPlaysB_toy`**, **`planPlaysB_came`**, **`planPlaysB_KR`**   it is true at the places of
                 Toy.lean (one tree sent in front) and ToyCame.lean (four), and at `piKRFull` (two)
  **`planPlays_KR`**   so `PlanPlays` holds at every job at `piKRFull` whose fresh table has come
                 earlier

Limits. It reads the plan alone. The first switch's declared opening of the old tree is read by no
clause but the kind's own test on the plan: it counts as old. The number of trees sent in front is
held against the place's own first free number: at `piKRFull` a copy against a copy. At a number of
trees above all own numbers that are opened the last clause is true for nothing. Four of
`piKRFull`'s numbers are a print's word, the number of trees sent in front among what they fix: see
that file's limits. The negative tests are evaluations by Lean's evaluator, outside the kernel: they
leave no theorem. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.Member (piKRFull)

variable {W X W' X' : Type}

/-- A job with a place and one word, and nothing else in it. own: the first fold sends its own
table. -/
def bare (p : P12) (own : Bool) : TestJob Unit Unit where
  p := p
  members := []
  fresh := if own then none else some (⟨p.place, 0⟩, 0)
  rec₀ := fun _ _ => Toy.noRec
  rows₀ := fun _ _ _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ => 0, fun _ => 0⟩
  trees₀ := fun _ _ _ _ => []

theorem bare_own (p : P12) (own : Bool) : (bare p own).fresh.isNone = own := by
  cases own <;> rfl

theorem tablesFitB_congr (J : TestJob W X) (J' : TestJob W' X') (hp : J.p = J'.p)
    (hf : J.fresh.isNone = J'.fresh.isNone) : tablesFitB J = tablesFitB J' := by
  unfold tablesFitB depthAt
  rw [hp, hf]

theorem newWideB_congr (J : TestJob W X) (J' : TestJob W' X') (hp : J.p = J'.p)
    (hf : J.fresh.isNone = J'.fresh.isNone) (decls : List Fmt.DeclaredRound) (sent : ℕ) :
    newWideB J decls sent = newWideB J' decls sent := by
  unfold newWideB sentBefore depthAt
  rw [hp, hf]

/-- The six clauses. -/
def planPlaysB (p : P12) (own : Bool) (sent : ℕ) : Bool :=
  match p.nums.stages with
  | s :: rest =>
    (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk &&
      decide ((laidOf p).map asked = [] :: bodyItems s rest) && tablesFitB (bare p own) &&
      decide (termLen p.nums.stages = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.length) &&
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.stored.isEmpty) &&
      newWideB (bare p own) (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds sent
  | [] => false

theorem planPlays_of_B (J : TestJob W X) (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: rest) (sent : ℕ)
    (h : planPlaysB J.p J.fresh.isNone sent = true) : PlanPlays J s rest sent := by
  unfold planPlaysB at h
  rw [hst] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
  refine ⟨a1, a2, ?_, ?_, a5, ?_⟩
  · rw [tablesFitB_congr J (bare J.p J.fresh.isNone) rfl (bare_own _ _).symm]
    exact a3
  · rw [hst]
    exact a4
  · rw [newWideB_congr J (bare J.p J.fresh.isNone) rfl (bare_own _ _).symm]
    exact a6

set_option maxRecDepth 100000 in
theorem planPlaysB_toy : planPlaysB Toy.p false 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem planPlaysB_came : planPlaysB ToyCame.p false 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem planPlaysB_KR : planPlaysB piKRFull false 2 = true := by decide +kernel

/-- **At the written place of the key file's test on the ranges.** -/
theorem planPlays_KR (J : TestJob W X) (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) :
    PlanPlays J s rest 2 :=
  planPlays_of_B J s rest hst 2 (by
    rw [hJ, hfr]
    exact planPlaysB_KR)

-- NEGATIVE: another number of trees sent in front; the other word on the fresh table
#guard !planPlaysB Toy.p false 2 && !planPlaysB piKRFull false 3
#guard !planPlaysB Toy.p true 1 && !planPlaysB piKRFull true 2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.bare_own
#print axioms ProofFile.Honest.K12.tablesFitB_congr
#print axioms ProofFile.Honest.K12.newWideB_congr
#print axioms ProofFile.Honest.K12.planPlays_of_B
#print axioms ProofFile.Honest.K12.planPlaysB_toy
#print axioms ProofFile.Honest.K12.planPlaysB_came
#print axioms ProofFile.Honest.K12.planPlaysB_KR
#print axioms ProofFile.Honest.K12.planPlays_KR
