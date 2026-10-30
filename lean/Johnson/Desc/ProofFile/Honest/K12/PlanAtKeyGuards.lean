-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlanAtKeyGuards.lean

The test on the plan (`planPlaysB`, PlanPlaysAt.lean in this folder) at the key file's two places
of the shared chain, by Lean's evaluator, clause by clause. PlanAtKeyKernel.lean imports this file,
so that the kernel is asked only where the evaluator has said yes: a `decide +kernel` that fails
reduces its term a second time to write its message, which at this size can take all the memory.

  `clausesB`   the six clauses of `planPlaysB` as a list, so that a no names its clause

Foretold, each line with its reason in the comment above it. `#eval` prints, `#guard` fails.

Limits. Evaluations outside the kernel: no theorem. The number of trees sent in front is read off
the place's own field `free`, so a yes here is a copy against a copy. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlanPlaysAt
import Johnson.Desc.K12.Law.PlacesKeyFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.PlanAtKey
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Member (piKUFull piKOFull)

/-- The six clauses of `planPlaysB`, in its order: plan, sorts, tables, count, stored, wide. -/
def clausesB (p : P12) (own : Bool) (sent : ℕ) : List Bool :=
  match p.nums.stages with
  | s :: rest =>
    [(proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk,
     decide ((laidOf p).map asked = [] :: bodyItems s rest),
     tablesFitB (bare p own),
     decide (termLen p.nums.stages = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.length),
     (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.stored.isEmpty,
     newWideB (bare p own) (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds sent]
  | [] => []

-- The two lines of the trial, and what each clause says.
#eval clausesB piKUFull false 3
#eval clausesB piKOFull true 7
-- The controls, printed, so that each no shows its clause.
#eval clausesB piKUFull true 3
#eval clausesB piKUFull false 2
#eval clausesB piKUFull false 4
#eval clausesB piKOFull false 7
#eval clausesB piKOFull true 6
#eval clausesB piKOFull true 8
-- The blind side, printed: above every own number opened the last clause is true for nothing.
#eval clausesB piKUFull false 7
#eval clausesB piKOFull true 11

-- The place's own words: the numbers that the two lines use.
#guard piKUFull.nums.free == 3 && !piKUFull.nums.ownMask
#guard piKOFull.nums.free == 7 && piKOFull.nums.ownMask

-- The clause list and the test are one, at each point of this file.
#guard [(piKUFull, false, 3), (piKOFull, true, 7), (piKUFull, true, 3), (piKUFull, false, 2),
  (piKUFull, false, 4), (piKOFull, false, 7), (piKOFull, true, 6), (piKOFull, true, 8)].all
  fun x => planPlaysB x.1 x.2.1 x.2.2 == (clausesB x.1 x.2.1 x.2.2).all id

-- THE TWO LINES. Foretold: yes.
#guard planPlaysB piKUFull false 3
#guard planPlaysB piKOFull true 7

-- CONTROLS. Foretold: no. The other word on the fresh table: the tables clause, since round 1
-- declares no tree at U and declares one at O.
#guard !planPlaysB piKUFull true 3
#guard !planPlaysB piKOFull false 7
-- Another number sent in front: the wide clause, since a new tree's number then meets the width of
-- another sending round.
#guard !planPlaysB piKUFull false 2
#guard !planPlaysB piKUFull false 4
#guard !planPlaysB piKOFull true 6
#guard !planPlaysB piKOFull true 8

end ProofFile.Honest.K12.PlanAtKey

#print axioms ProofFile.Honest.K12.PlanAtKey.clausesB
