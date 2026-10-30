-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnLinesGuards.lean: the public lines on the members and the trees
of the key file's own test, by Lean's evaluator, printed. OwnKernel.lean asks the kernel what is said yes.

  `msOf`       the three members' shapes, as a job of this test has them, at the two sendings' parameters and
               the shared chain's
  `msOwn`      at the written values
  `takenOwn`   the sources of the trees that the test's first round of positions opens
  `opensOwn`   the test `opensFitB` at a list of depths, a list of sources and a number of trees sent

Limits. Evaluations outside the kernel: no theorem. Nothing of a run.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnGuards
import E2E.KeyProverSideOfOwnTest
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.ManyFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts T12)
open H2K.Member (piKWFull)
open ProofFile.Honest.Sh (thinOf)
open ProofFile.Honest.K12.Light (MemShape firstsOf manyFitsS)
open ProofFile.Honest.K12.AtProof (shapesW memShape treesW placeW)
open Johnson.Prover.Send (shapeAt)
open AtPublicFiles.KeyLay (parIK parWK pWK)
open AtPublicFiles.AtFiles.Full (QK PF)

/-- **The three members' shapes.** -/
def msOf (PI PW : VerifiableInference.Desc.K1.Par) (Q : Desc.K14.P14) : List MemShape :=
  [memShape (shapeAt PI (PI.sent.size - 1))
      ((firstsOf (shapesW PI PW ((ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape)).getD 0
        (none, none)),
    memShape (shapeAt PW 0)
      ((firstsOf (shapesW PI PW ((ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape)).getD 1
        (none, none)),
    memShape ((ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape
      ((firstsOf (shapesW PI PW ((ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape)).getD 2
        (none, none))]

/-- At the written values. -/
def msOwn : List MemShape := msOf parIK parWK QK

/-- The sources of the three trees. -/
def takenOwn : List Fmt.TreeSource := [.taken 0 0, .taken 0 5, .taken 1 1]

/-- The test on the openings at the own test. -/
def opensOwn (depths : List ℕ) (src : List Fmt.TreeSource) (sent : ℕ) : Bool :=
  opensFitB false piKWFull.nums.stages (proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds depths src sent

#eval msOwn
#eval (treesW piKWFull).map (·.1)
#eval opensOwn [13, 22, 22] takenOwn 0
#eval opensOwn [22, 13, 22] takenOwn 0
#eval opensOwn [13, 22, 22] takenOwn 1

end ProofFile.Honest.K12.AtKey
