-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnGuards.lean: the public lines at the key file's own test
(its last chain's proximity test, at the place `piKWFull`), by Lean's evaluator: printed, so that
each no shows its clause. OwnKernel.lean asks the kernel what is said yes here.

  `shapeAtOwn`   the last chain's shape in front of the own test: the run on shapes (`ZW`,
                 E2E/KeyShapeOwn.lean) over the chain's first two blocks, from the chain's first shape
                 (`X0`, E2E/KeyShapeSharedFull.lean)
  `testAtOwn`    the test's own shape there: the core, the own group, nothing passing, the mask
  `frontClauses` the six clauses of `frontFiveB` (K12/FrontAtShape.lean) at a shape
  `blockBits`    for each run and digit of a lookup of the ranges' proof, the logarithm of the first
                 aligned block of rows of that run: above 0 the row weights there have a written-out
                 factor (`Wf.weightsFrom`)

Limits. Evaluations outside the kernel: no theorem. Public numbers and shapes: nothing of a run, no
value of a state. That a state of a run has these shapes is not said here.
-/
import E2E.KeyShapeOwn
import E2E.KeyShapeSharedFull
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K12.PlanAtKeyGuards
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Member (piKWFull)
open ProofFile.Honest.Sh (TestSh thinOf)
open AtPublicFiles.AtFiles (Sh₃ ZW SF CF)
open AtPublicFiles.AtFiles.Full (X0)

/-- The last chain's shape in front of the own test. -/
def shapeAtOwn : Option Sh₃ := X0.bind fun a => (ZW.run 2 a).toOption

/-- The test's own shape there. -/
def testAtOwn : Option TestSh :=
  shapeAtOwn.map fun a => ⟨a.1, a.2.own, .nothing, a.2.mask⟩

/-- The six clauses of `frontFiveB`, in its order. -/
def frontClauses (p : P12) (K : Codes) (N : TestSh) : List Bool :=
  [decide (N.core.st.codes = K),
   ProofFile.Honest.Sh.doorB p (stA p) (stN p) (((laidOf p).take 1).map (·.1)) (lettersOf p (stA p) (stN p)).i
     ((lettersOf p (stA p) (stN p)).n.code, (lettersOf p (stA p) (stN p)).n.maskCode) N,
   N.mask.isSome,
   (match N.pass with
     | .nothing => true
     | _ => false),
   frontPlainB₀ p (thinOf N), ProofFile.Honest.K12.Thin.frontPubB p (thinOf N)]

/-- For each run and digit of a lookup, the logarithm of the first aligned block of its rows. -/
def blockBits : List ℕ :=
  Lk6.AtPlan.keyFull.ranges.x.lookups.flatMap fun l => l.parts.flatMap fun q => q.runs.flatMap fun r =>
    l.digitWeight.zipIdx.map fun w =>
      Wf.rowBlockBits SF.kRow (r.firstRow + w.2 * r.stride)
        (r.firstRow + w.2 * r.stride + r.places) SF.kRow 0

#eval (piKWFull.nums.free, piKWFull.nums.ownMask, piKWFull.early, piKWFull.answers)
#eval ProofFile.Honest.K12.PlanAtKey.clausesB piKWFull false 0
#eval ProofFile.Honest.K12.PlanAtKey.clausesB piKWFull true 0
#eval ProofFile.Honest.K12.PlanAtKey.clausesB piKWFull false 1
#eval planNo piKWFull CF 2
#eval planNo piKWFull CF 3
#eval planNo piKWFull CF 4
#eval formPubB piKWFull
#eval (SF.kRow, SF.matrixRows, blockBits.length, blockBits.foldl max 0)

end ProofFile.Honest.K12.AtKey
