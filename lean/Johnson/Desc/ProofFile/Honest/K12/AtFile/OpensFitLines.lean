-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OpensFitLines.lean: `opensFitB` (K12/OpensFitB.lean) at the
written places of the test on G_u and of the last chain's test, first by Lean's evaluator, then by the
kernel: what the test's first reading round opens of older trees, at their depths and sources. This is the
clause `OpensFit` of `K12At.opens`. It can say no.

  `opensFit_U`, `opensFit_W`   the test says yes: at G_u the depths 24 and 13 at own 0 and own 2, three
                 trees in front; at the last chain the depths 13, 22, 22 at the three trees taken over,
                 no own tree in front
  `opensFit_U_sent`, `opensFit_U_depth`, `opensFit_U_src`, `opensFit_W_sent`, `opensFit_W_src`   controls: one
                 argument changed: no
  `opensFit_head_U`   `OpensFit` at every job at the seated place of the test on G_u whose fresh table
                 has come earlier

Limits. At G_omega the first fold sends its own table, and `OpensFit` has a twin there: not here. Public
numbers: nothing on what a table holds. The seated place of the last chain's test: not carried here.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableShared
import AtFullSide.K12.RestTiesAtHeadW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest.K12 (TestJob opensFitB OpensFit opensFit_of_B)
open ProofFile.Honest.K12.AtProof (fourOf)
open H2K.Member (piUFull piWFull)

/-- The sources of the trees that the test on G_u opens. -/
def srcU : List Fmt.TreeSource := [.own 0, .own 2]

-- Foretold: yes at both. Controls: no.
#guard opensFitB false piUFull.nums.stages (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds [24, 13] srcU 3
#guard opensFitB false piWFull.nums.stages (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds [13, 22, 22]
  takenLast 0
#guard !opensFitB false piUFull.nums.stages (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds [24, 13] srcU 4
#guard !opensFitB false piUFull.nums.stages (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds [24, 14] srcU 3
#guard !opensFitB false piUFull.nums.stages (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds [24, 13]
  [.own 0, .own 1] 3
#guard !opensFitB false piWFull.nums.stages (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds [13, 22, 22]
  takenLast 1
#guard !opensFitB false piWFull.nums.stages (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds [13, 22, 22]
  takenLast.reverse 0

theorem opensFit_U : opensFitB false piUFull.nums.stages (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds
    [24, 13] srcU 3 = true := by decide +kernel

theorem opensFit_W : opensFitB false piWFull.nums.stages (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds
    [13, 22, 22] takenLast 0 = true := by decide +kernel

theorem opensFit_U_sent : opensFitB false piUFull.nums.stages
    (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds [24, 13] srcU 4 = false := by decide +kernel

theorem opensFit_U_depth : opensFitB false piUFull.nums.stages
    (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds [24, 14] srcU 3 = false := by decide +kernel

theorem opensFit_U_src : opensFitB false piUFull.nums.stages
    (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds [24, 13] [.own 0, .own 1] 3 = false := by
  decide +kernel

theorem opensFit_W_sent : opensFitB false piWFull.nums.stages
    (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds [13, 22, 22] takenLast 1 = false := by
  decide +kernel

theorem opensFit_W_src : opensFitB false piWFull.nums.stages
    (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds [13, 22, 22] takenLast.reverse 0 = false := by
  decide +kernel

variable {W X : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **`OpensFit` at every job at the seated place of the test on G_u** whose fresh table has come
earlier. -/
theorem opensFit_head_U (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) :
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds [24, 13]
      (fun k => srcU.getD k (.own 0)) 3 :=
  opensFit_of_B _ _ _ _ _ (by
    rw [hfr, hJ, rounds_head_U h, congrArg (·.stages) (ProofFile.Honest.K12.Light.nums_head_U h)]
    exact opensFit_U)

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.opensFit_U
#print axioms ProofFile.Honest.K12.AtFile.opensFit_W
#print axioms ProofFile.Honest.K12.AtFile.opensFit_U_sent
#print axioms ProofFile.Honest.K12.AtFile.opensFit_U_depth
#print axioms ProofFile.Honest.K12.AtFile.opensFit_U_src
#print axioms ProofFile.Honest.K12.AtFile.opensFit_W_sent
#print axioms ProofFile.Honest.K12.AtFile.opensFit_W_src
#print axioms ProofFile.Honest.K12.AtFile.opensFit_head_U
