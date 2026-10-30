-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointFit.lean: a closed test at the written sizes: nine of
the eleven fields of OmegaAtW (WJointTaken.lean), all but mems and tree: at every typed size, over a
proof file's own codes, at the written sendings and the written place's first stage, they evaluate
to true.

  omegaFitsB           the test
  omegaFitsW           an evaluation in Lean's kernel

Limits. At parGF, parWF and piWFull's first stage, not at a job's own first stage: that a job at a
public part has these numbers is another statement. hcover, hdepth and hdue of WJointArms.lean are
not tested here. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (OracleShape)
open ProofFile.Honest.K12.Light (firstsOf sameCode shapeAt mineOf widthFits)
open ProofFile.Honest.K14 (SendPub jobOmega)

/-- Two blocks of rows do not overlap. -/
def clearB (a b : ProofFile.Honest.K12.Light.MemShape) : Bool :=
  a.mainRows == 0 || decide (a.mainFirst + a.mainRows ≤ b.mainFirst) ||
    decide (b.mainFirst + b.mainRows ≤ a.mainFirst)

/-- **The test.** -/
def omegaFitsB (A : SendPub) : Bool :=
  let sO := ((jobOmega A).Q.sent.getD 0 default).shape
  let sh := shapesW VerifiableInference.Desc.K1.parGF VerifiableInference.Desc.K1.parWF sO
  let fs := firstsOf sh
  let ms := sh.zipIdx.map fun x => memShape x.1 (fs.getD x.2 (none, none))
  let s := H2K.Member.piWFull.nums.stages.headD default
  let m0 := ms.getD 0 default
  let m1 := ms.getD 1 default
  let m2 := ms.getD 2 default
  decide (s.h ≤ s.k) &&
    sameCode ((jobOmega A).Q.codes.base.getD (shapeAt (jobOmega A) 0).code default) s.C &&
    (m2.base == false) && decide (m2.mainFirst + m2.mainRows ≤ 2 ^ s.k) &&
    clearB m0 m2 && clearB m1 m2 && (mineOf (jobOmega A) 0 == [0]) &&
    ((shapeAt (jobOmega A) 0).maskRows == 0) && widthFits (jobOmega A) 0

set_option maxRecDepth 1000000 in
/-- **The test says yes at the typed sizes.** An evaluation in Lean's kernel. -/
theorem omegaFitsW : (VerifiableInference.Desc.K1.realSized.all fun y =>
    omegaFitsB (ProofFile.Honest.K12.Light.planOf y.2 y.1.shape)) = true := by decide +kernel

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.clearB
#print axioms ProofFile.Honest.K12.AtProof.omegaFitsB
#print axioms ProofFile.Honest.K12.AtProof.omegaFitsW
