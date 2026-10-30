-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/EndShapeRun.lean: a closed test: the guards on the shape of the
proof file's shared chain return over its twelve members, from the first state's shape, at the
typed sizes and the written tests.

  runOK, shape_run_real   the test, and its evaluation in Lean's kernel

Limits. At the written tests piUFull, piOFull. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.EndAtProof
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open _root_.Desc.K14 (P14)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.K1 (realSized)
open _root_.Desc.K14.Shape (sh2)
open H2K.Member (piUFull piOFull)

/-- The test. -/
def runOK (Q : P14) (pU pO : P12) : Bool :=
  (ZP Q ((_root_.Desc.K14.withU Q.S).getD #[]) pU pO (fun _ _ _ _ => true)).yes
    (sh2 (_root_.Desc.K14.first Q.codes (_root_.Desc.K14.Honest.keyW Q.par.S.fold.index)), true) 12

/-- **The guards' run returns at the typed sizes.** An evaluation in Lean's kernel. -/
theorem shape_run_real : (realSized.all fun q =>
    runOK (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape).P piUFull piOFull) = true := by decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.runOK
#print axioms ProofFile.Honest.K12.AtFile.shape_run_real
