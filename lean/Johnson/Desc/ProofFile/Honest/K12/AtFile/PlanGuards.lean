-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/PlanGuards.lean: the test on the plan (`planPlaysB`,
K12/PlanPlaysAt.lean) at the proof file's three written places of a proximity test that the request's
prover plays with the shared and the last chain, by Lean's evaluator, clause by clause.
PlanKernel.lean imports this file, so that the kernel is asked only where the evaluator has said yes:
a `decide +kernel` that fails reduces its term a second time to write its message, which at this size
can take all the memory.

  `planClauses`   the six clauses of `planPlaysB` as a list, so that a no names its clause

The three numbers: the trees that the chain has sent in front of the test: 3 in front of the test on
G_u, 7 in front of the test on G_omega, 0 in front of the last chain's test. Each is the place's own
field `free`. The word on the fresh table: false at G_u and at the last chain's test, where the fresh
table has come earlier; true at G_omega, where the first fold sends its own.

Foretold, each line with its reason in the comment above it. `#eval` prints, `#guard` fails.

Limits. Evaluations outside the kernel: no theorem. The number of trees sent in front is read off the
place's own field `free`, so a yes here is a copy against a copy: that the chain has sent so many is
not said here. The written places bear other pieces than the seated ones; the test reads no piece:
PlanAtSeat.lean carries it to the seats. At a number above every own tree that is opened the last
clause is true for nothing. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlanPlaysAt
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Member (piUFull piOFull piWFull)

/-- The six clauses of `planPlaysB`, in its order: plan, sorts, tables, count, stored, wide. -/
def planClauses (p : P12) (own : Bool) (sent : ℕ) : List Bool :=
  match p.nums.stages with
  | s :: rest =>
    [(proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk,
     decide ((laidOf p).map asked = [] :: bodyItems s rest),
     tablesFitB (bare p own),
     decide (termLen p.nums.stages = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.length),
     (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.stored.isEmpty,
     newWideB (bare p own) (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds sent]
  | [] => []

-- The three lines, and what each clause says.
#eval planClauses piUFull false 3
#eval planClauses piOFull true 7
#eval planClauses piWFull false 0
-- The controls, printed, so that each no shows its clause.
#eval planClauses piUFull true 3
#eval planClauses piUFull false 2
#eval planClauses piUFull false 4
#eval planClauses piOFull false 7
#eval planClauses piOFull true 6
#eval planClauses piOFull true 8
#eval planClauses piWFull true 0
#eval planClauses piWFull false 1
-- The blind side, printed: above every own number opened the last clause is true for nothing.
#eval planClauses piUFull false 7
#eval planClauses piOFull true 11
#eval planClauses piWFull false 4

-- The places' own words: the numbers that the three lines use.
#guard piUFull.nums.free == 3 && !piUFull.nums.ownMask
#guard piOFull.nums.free == 7 && piOFull.nums.ownMask
#guard piWFull.nums.free == 0 && !piWFull.nums.ownMask

-- The clause list and the test are one, at each point of this file.
#guard [(piUFull, false, 3), (piOFull, true, 7), (piWFull, false, 0), (piUFull, true, 3),
  (piUFull, false, 2), (piUFull, false, 4), (piOFull, false, 7), (piOFull, true, 6),
  (piOFull, true, 8), (piWFull, true, 0), (piWFull, false, 1)].all
  fun x => planPlaysB x.1 x.2.1 x.2.2 == (planClauses x.1 x.2.1 x.2.2).all id

-- THE THREE LINES. Foretold: yes.
#guard planPlaysB piUFull false 3
#guard planPlaysB piOFull true 7
#guard planPlaysB piWFull false 0

-- CONTROLS. Foretold: no. The other word on the fresh table: the tables clause: at G_u and at the
-- last chain's test round 1 declares no tree; at G_omega it declares one.
#guard !planPlaysB piUFull true 3
#guard !planPlaysB piOFull false 7
#guard !planPlaysB piWFull true 0
-- Another number sent in front: the wide clause, since a new tree's number then meets the width of
-- another sending round.
#guard !planPlaysB piUFull false 2
#guard !planPlaysB piUFull false 4
#guard !planPlaysB piOFull true 6
#guard !planPlaysB piOFull true 8
#guard !planPlaysB piWFull false 1

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.planClauses
