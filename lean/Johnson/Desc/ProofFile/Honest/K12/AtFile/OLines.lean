-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OLines.lean: the closed lines of the proof file's proximity test
on G_omega, at the typed sizes and the written places, first by Lean's evaluator, then by the kernel, each
but the plain facts on the place (`first_k_O`, `stages_O`, `rounds_len_O`, `hk_O`, `count_O`) with a control that
says no. They decide whether the premises of the test's own-table laws (K12/Own/) can
be had at the proof file at all.

  `omegaShape`   the one shape of the door's state (`shape_doorOmegaF`, K12/DoorsByShape.lean) at a sized value
  `rowsMembers`, `group_real`   the group under test has one open row, and the members 2 and 3: the items at
                 border 10 speak of the group's first open row alone, so a second one would be a wall
  `five_real`   all the shape's clauses in one (`frontOwnFiveB`, K12/Own/FrontOwnFive.lean)
  `ts_real_O`   the plain data have three trees
  `treesAtOmega`, `many_real_O`   the job's trees; `manyFitsS` (K12/ManyFits.lean) at the job's members and trees
  `width_real_O`, `col_real_O`, `fresh_O`   the sendings' two tests at the test on G_omega; the place's flag
  `srcO`, `opensFit_O`   what the test's first reading round opens: depths 22, 13, 13 at own 1, own 2 and
                 own 7, seven trees in front: own 7 is the fold's own tree, sent in the test
  `first_k_O`, `stages_O`   k = h + g at the first stage; there are two stages or more
  `bat_O`   the batching's one declared round passes its test on the round
  `rounds_len_O`, `hk_O`, `count_O`   round 1 stands; h ≤ k at every stage; as many trees declared as stages

The controls: a group that is not there; a mask named; the other test's shape; a tree or a member left
out; another number of trees in front; another depth, source or word on the fresh table; codes that
hold nothing.

Limits.
- The statements of the form (realSized.all …) = true would be true for nothing if realSized were none; it
  is not (`real_members`, Johnson/Desc/K1/Law/CondReal.lean).
- Public numbers and shapes: no state of a run. That the shape is the state's at a run is
  `shape_head_OmegaF` (K12/FrontAtHead.lean), under its premises, and a yes at the shape is true of the
  fall-back too: no statement that the state on entry is the verifier's.
- The written places are closed terms: OAtHead.lean carries these lines to the seated places.
- The full size alone. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.FrontOwnFive
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Ground.Sh (GrpSh)
open H2K.JointK (laidOf)
open H2K.Member (piUFull piOFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.K14 (jobOmega)
open ProofFile.Honest.K12 (opensFitB)
open ProofFile.Honest.K12.Own (frontOwnFiveB)
open ProofFile.Honest.K12.Light (Piece planOf sentOf endOmega emptyOmega tsLenOf manyFitsS
  widthFits colFitsOmega freshFitsOmega)
open ProofFile.Honest.Sh (TestSh thinOf)

/-- **The one shape of the door's state at the test on G_omega**, at a sized value. -/
def omegaShape (q : OnBytes.Params.LinSized × OnBytes.Codes) : TestSh :=
  Desc.K14.Shape.doorO (endOmega (Light.planOf q.2 q.1.shape).P (sentOf q.1.shape) piUFull)

/-- The one shape of the door's state at the test on G_u, for a control. -/
def uShape (q : OnBytes.Params.LinSized × OnBytes.Codes) : TestSh :=
  Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf (Light.planOf q.2 q.1.shape).P (sentOf q.1.shape))

/-- Of a group of the shape: the number of open rows, and the members. -/
def rowsMembers (G : GrpSh) : Nat × List Nat := (G.kinds.length, G.members)

/-- The job's list of trees at the test on G_omega (`jobAtOmega`, K12/JobShared.lean). -/
def treesAtOmega (p : P12) : List (Nat × List Piece) :=
  [(Light.depthOf p 0, [.main 0]), (Light.depthOf p 1, [.mask 1]),
    ((p.nums.stages.headD default).Z.a, [.fresh])]

/-- The sources of the trees that the test on G_omega opens. -/
def srcO : List Fmt.TreeSource := [.own 1, .own 2, .own 7]

-- Printed, so that each no shows where it stands.
#eval realSized.map fun q => ((omegaShape q).g, (omegaShape q).mask)
#eval realSized.map fun q => (omegaShape q).core.st.groups.map rowsMembers
#eval realSized.map fun q => frontOwnFiveB piOFull q.2 (omegaShape q)
#eval realSized.map fun q => tsLenOf piOFull (thinOf (omegaShape q))
#eval realSized.map fun q => manyFitsS piOFull ((emptyOmega q.2 q.1.shape).mems.map (·.shape))
  (treesAtOmega piOFull) (thinOf (omegaShape q))
#eval (treesAtOmega piOFull).map (·.1)
#eval realSized.map fun q => (widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 0,
  widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 1, colFitsOmega (Light.planOf q.2 q.1.shape) piOFull)
#eval opensFitB true piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13]
  srcO 7

-- THE GROUP. Foretold: one open row, members 2 and 3. Control: the group of the test on G_u.
#guard realSized.all fun q => decide
  (((omegaShape q).core.st.groups[(omegaShape q).g]?).map rowsMembers = some (1, [2, 3]))
#guard realSized.all fun q => decide
  (((omegaShape q).core.st.groups[0]?).map rowsMembers ≠ some (1, [2, 3]))

-- ALL THE SHAPE's CLAUSES. Foretold: yes. Controls: a mask named; another group; the other test's shape.
#guard realSized.all fun q => frontOwnFiveB piOFull q.2 (omegaShape q)
#guard realSized.all fun q => !frontOwnFiveB piOFull q.2 { omegaShape q with mask := some 0 }
#guard realSized.all fun q => !frontOwnFiveB piOFull q.2 { omegaShape q with g := 99 }
#guard realSized.all fun q => !frontOwnFiveB piOFull q.2 (uShape q)

-- THE PLAIN DATA's TREES. Foretold: three. Control: another group.
#guard realSized.all fun q => tsLenOf piOFull (thinOf (omegaShape q)) == 3
#guard realSized.all fun q => tsLenOf piOFull (thinOf { omegaShape q with g := 99 }) != 3

-- THE JOB's MEMBERS AND TREES. Foretold: yes. Controls: a tree left out; a member left out.
#guard realSized.all fun q => manyFitsS piOFull ((emptyOmega q.2 q.1.shape).mems.map (·.shape))
  (treesAtOmega piOFull) (thinOf (omegaShape q))
#guard realSized.all fun q => !manyFitsS piOFull ((emptyOmega q.2 q.1.shape).mems.map (·.shape))
  (treesAtOmega piOFull).dropLast (thinOf (omegaShape q))
#guard realSized.all fun q => !manyFitsS piOFull
  ((emptyOmega q.2 q.1.shape).mems.map (·.shape)).dropLast (treesAtOmega piOFull)
  (thinOf (omegaShape q))
#guard (treesAtOmega piOFull).map (·.1) == [22, 13, 13]
#guard (treesAtOmega piOFull).map (·.1) != [22, 13, 14]

-- THE SENDINGS. Foretold: yes. Controls: no.
#guard realSized.all fun q => widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 0 &&
  widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 1
#guard realSized.all fun q => !widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 5
#guard realSized.all fun q => colFitsOmega (Light.planOf q.2 q.1.shape) piOFull
#guard realSized.all fun q =>
  !colFitsOmega ⟨{ (Light.planOf q.2 q.1.shape).P with codes := ⟨#[], #[]⟩ }, 0⟩ piOFull
#guard freshFitsOmega piOFull
#guard !freshFitsOmega piUFull

-- THE OPENINGS. Foretold: yes. Controls: one tree more in front; another depth; another source; the
-- other word on the fresh table; the fresh tree left out.
#guard opensFitB true piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13]
  srcO 7
#guard !opensFitB true piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13]
  srcO 8
#guard !opensFitB true piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [21, 13, 13]
  srcO 7
#guard !opensFitB true piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13]
  [.own 0, .own 2, .own 7] 7
#guard !opensFitB false piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13]
  srcO 7
#guard !opensFitB true piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13]
  [.own 1, .own 2] 7

theorem group_real : (realSized.all fun q => decide
    (((omegaShape q).core.st.groups[(omegaShape q).g]?).map rowsMembers = some (1, [2, 3]))) = true := by
  decide +kernel

theorem group_real_bent : (realSized.all fun q => decide
    (((omegaShape q).core.st.groups[0]?).map rowsMembers ≠ some (1, [2, 3]))) = true := by
  decide +kernel

theorem five_real : (realSized.all fun q => frontOwnFiveB piOFull q.2 (omegaShape q)) = true := by
  decide +kernel

theorem five_real_mask :
    (realSized.all fun q => !frontOwnFiveB piOFull q.2 { omegaShape q with mask := some 0 }) = true := by
  decide +kernel

theorem five_real_g :
    (realSized.all fun q => !frontOwnFiveB piOFull q.2 { omegaShape q with g := 99 }) = true := by
  decide +kernel

theorem five_real_U : (realSized.all fun q => !frontOwnFiveB piOFull q.2 (uShape q)) = true := by
  decide +kernel

theorem ts_real_O :
    (realSized.all fun q => decide (tsLenOf piOFull (thinOf (omegaShape q)) = 3)) = true := by
  decide +kernel

theorem ts_real_O_g :
    (realSized.all fun q => decide (tsLenOf piOFull (thinOf { omegaShape q with g := 99 }) ≠ 3)) =
      true := by
  decide +kernel

theorem many_real_O : (realSized.all fun q =>
    manyFitsS piOFull ((emptyOmega q.2 q.1.shape).mems.map (·.shape)) (treesAtOmega piOFull)
      (thinOf (omegaShape q))) = true := by
  decide +kernel

theorem many_real_O_trees : (realSized.all fun q =>
    !manyFitsS piOFull ((emptyOmega q.2 q.1.shape).mems.map (·.shape))
      (treesAtOmega piOFull).dropLast (thinOf (omegaShape q))) = true := by
  decide +kernel

theorem many_real_O_mems : (realSized.all fun q =>
    !manyFitsS piOFull ((emptyOmega q.2 q.1.shape).mems.map (·.shape)).dropLast
      (treesAtOmega piOFull) (thinOf (omegaShape q))) = true := by
  decide +kernel

theorem trees_O : (treesAtOmega piOFull).map (·.1) = [22, 13, 13] := by decide +kernel

theorem trees_O_bent : (treesAtOmega piOFull).map (·.1) ≠ [22, 13, 14] := by decide +kernel

theorem width_real_O : (realSized.all fun q => widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 0 &&
    widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 1) = true := by
  decide +kernel

theorem width_real_O_five :
    (realSized.all fun q => !widthFits (jobOmega (Light.planOf q.2 q.1.shape)) 5) = true := by
  decide +kernel

theorem col_real_O : (realSized.all fun q => colFitsOmega (Light.planOf q.2 q.1.shape) piOFull) = true := by
  decide +kernel

theorem col_real_O_codes : (realSized.all fun q =>
    !colFitsOmega ⟨{ (Light.planOf q.2 q.1.shape).P with codes := ⟨#[], #[]⟩ }, 0⟩ piOFull) = true := by
  decide +kernel

theorem fresh_O : freshFitsOmega piOFull = true := by decide +kernel

theorem fresh_O_place : freshFitsOmega piUFull = false := by decide +kernel

theorem opensFit_O : opensFitB true piOFull.nums.stages (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds
    [22, 13, 13] srcO 7 = true := by decide +kernel

theorem opensFit_O_sent : opensFitB true piOFull.nums.stages
    (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13] srcO 8 = false := by decide +kernel

theorem opensFit_O_depth : opensFitB true piOFull.nums.stages
    (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [21, 13, 13] srcO 7 = false := by decide +kernel

theorem opensFit_O_src : opensFitB true piOFull.nums.stages
    (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13] [.own 0, .own 2, .own 7] 7 = false := by
  decide +kernel

theorem opensFit_O_word : opensFitB false piOFull.nums.stages
    (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13, 13] srcO 7 = false := by decide +kernel

theorem opensFit_O_two : opensFitB true piOFull.nums.stages
    (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds [22, 13] [.own 1, .own 2] 7 = false := by
  decide +kernel

/-- k = h + g at the first stage of the written place. -/
theorem first_k_O : (piOFull.nums.stages.headD default).k =
    (sgOf (piOFull.nums.stages.headD default)).h + (sgOf (piOFull.nums.stages.headD default)).g := by
  decide +kernel

/-- The written place has two stages or more. -/
theorem stages_O : ∃ a next rest, piOFull.nums.stages = a :: next :: rest := ⟨_, _, _, rfl⟩

/-- The batching's one declared round. -/
theorem bat_O : Johnson.Prover.Link.batCut (((laidOf piOFull).take 1).map (·.1)) = true := by
  decide +kernel

/-- Control: two rounds are no batching's. -/
theorem bat_O_two : Johnson.Prover.Link.batCut (((laidOf piOFull).take 2).map (·.1)) = false := by
  decide +kernel

/-- The test has a round 1. -/
theorem rounds_len_O : 1 < (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds.length := by decide +kernel

/-- h ≤ k at every stage of the written place. -/
theorem hk_O : (piOFull.nums.stages.all fun a => decide (a.h ≤ a.k)) = true := by decide +kernel

/-- The written place's messages: as many trees as stages. -/
theorem count_O : (piOFull.oracles.flatMap id).length = piOFull.nums.stages.length := by decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.omegaShape
#print axioms ProofFile.Honest.K12.AtFile.treesAtOmega
#print axioms ProofFile.Honest.K12.AtFile.group_real
#print axioms ProofFile.Honest.K12.AtFile.group_real_bent
#print axioms ProofFile.Honest.K12.AtFile.five_real
#print axioms ProofFile.Honest.K12.AtFile.five_real_mask
#print axioms ProofFile.Honest.K12.AtFile.five_real_g
#print axioms ProofFile.Honest.K12.AtFile.five_real_U
#print axioms ProofFile.Honest.K12.AtFile.ts_real_O
#print axioms ProofFile.Honest.K12.AtFile.ts_real_O_g
#print axioms ProofFile.Honest.K12.AtFile.many_real_O
#print axioms ProofFile.Honest.K12.AtFile.many_real_O_trees
#print axioms ProofFile.Honest.K12.AtFile.many_real_O_mems
#print axioms ProofFile.Honest.K12.AtFile.trees_O
#print axioms ProofFile.Honest.K12.AtFile.width_real_O
#print axioms ProofFile.Honest.K12.AtFile.width_real_O_five
#print axioms ProofFile.Honest.K12.AtFile.col_real_O
#print axioms ProofFile.Honest.K12.AtFile.col_real_O_codes
#print axioms ProofFile.Honest.K12.AtFile.fresh_O
#print axioms ProofFile.Honest.K12.AtFile.fresh_O_place
#print axioms ProofFile.Honest.K12.AtFile.opensFit_O
#print axioms ProofFile.Honest.K12.AtFile.opensFit_O_sent
#print axioms ProofFile.Honest.K12.AtFile.opensFit_O_depth
#print axioms ProofFile.Honest.K12.AtFile.opensFit_O_src
#print axioms ProofFile.Honest.K12.AtFile.opensFit_O_word
#print axioms ProofFile.Honest.K12.AtFile.opensFit_O_two
#print axioms ProofFile.Honest.K12.AtFile.first_k_O
#print axioms ProofFile.Honest.K12.AtFile.stages_O
#print axioms ProofFile.Honest.K12.AtFile.bat_O
#print axioms ProofFile.Honest.K12.AtFile.rounds_len_O
#print axioms ProofFile.Honest.K12.AtFile.hk_O
#print axioms ProofFile.Honest.K12.AtFile.count_O
#print axioms ProofFile.Honest.K12.AtFile.bat_O_two
#print axioms ProofFile.Honest.K12.AtFile.trees_O_bent
