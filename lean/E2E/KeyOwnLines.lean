-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnLines.lean: closed lines at the key file's own proximity test, at the written place `piKWFull` and the shape at
which the chain reaches the test. Each is a test that can say no, by Lean's kernel.

  `A2`, `testOf`: the shape at border 2, and the test's state on entry on it.
  `five_KW`: the five clauses of `FrontAsksD` that stand on the shape (`frontFiveB`).
  `many_KW`: the members' tests on the trees (`manyFitsS`).
  `formPub_KW`, `termLen_KW`, `planPlays_KW`: the plan's.

A NO IN ANY LINE SAYS THAT THE ROAD THROUGH `OwnFrontDense` IS WRONG AT THE KEY FILE, OR THAT THE LINE IS MISTYPED.
Limits. Closed terms: no tie here to a state. The written place is the one in scope only.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyShapeThirdFull
import E2E.KeyJobW
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShapeDense
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAtDense
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.ProofFile.Honest.K12.PlanPlaysAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (ownTest)
open AtPublicFiles.AtFiles (Sh₃ Z₃ gOwn SF CF)
open AtPublicFiles.AtFiles.Full (A0 PF)
open H2K.Member (piKWFull)
open ProofFile.Honest.Sh (TestSh thinOf)
open ProofFile.Honest.K12 (frontFiveB formPubB termLen planPlaysB)
open ProofFile.Honest.K12.Light (manyFitsS firstsOf)
open ProofFile.Honest.K12.AtProof (shapesW treesW memShape)
open AtPublicFiles.KeyLay (parIK parWK shapeOK)

/-- The shape at the test, at the written terms. -/
def A2 : Sh₃ :=
  ((Z₃ SF (ownTest PF).rounds (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W)) fun _ _ _ => true).run 2 A0).toOption.getD A0

/-- The test's state on entry, on the shape. -/
def testOf (a : Sh₃) : TestSh := ⟨a.1, a.2.own, .nothing, a.2.mask⟩

/-- The members' shapes at the written sizes. -/
def msKW : List ProofFile.Honest.K12.Light.MemShape :=
  let sh := shapesW parIK parWK shapeOK
  let fs := firstsOf sh
  sh.zipIdx.map fun x => memShape x.1 (fs.getD x.2 (none, none))

theorem five_KW : frontFiveB piKWFull CF (testOf A2) = true := by decide +kernel

theorem many_KW : manyFitsS piKWFull msKW (treesW piKWFull) (thinOf (testOf A2)) = true := by
  decide +kernel

theorem formPub_KW : formPubB piKWFull = true := by decide +kernel

theorem termLen_KW : termLen piKWFull.nums.stages =
    (proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds.length := by decide +kernel

theorem planPlays_KW : planPlaysB piKWFull false 0 = true := by decide +kernel

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.five_KW
#print axioms AtPublicFiles.KeyLastChain.many_KW
#print axioms AtPublicFiles.KeyLastChain.formPub_KW
#print axioms AtPublicFiles.KeyLastChain.termLen_KW
#print axioms AtPublicFiles.KeyLastChain.planPlays_KW
