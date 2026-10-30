-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesPlanDense.lean: the "dense" twin of
`behind_of_plan_trees` (TreesPlan.lean in this folder).

What it is. The old statements and structures hold or take `ShapeAsks` (PlanB.lean in the folder
above), whose field `plainRows` asks that no open row and no sample row of the whole statement on
entry has a written-out variable (`stPlainB`, Johnson/Desc/Ground/Shape/Marks.lean). The twins hold
or take `ShapeAsksD` (PlanBDense.lean there), which asks `DenseRow` of the rows taken in at the
group under test. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of a row has a
written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables where every
tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter.

Why. The only place where the old chain spends its hypothesis is the field `dense` of the library's
`TestFront`, which `testFront_of` fills from `PlainRow` by `denseRow_of_plain`. So the weaker
hypothesis is enough. That a row taken in at the first chain's proximity test has written-out
variables is read off the description's text; no theorem in these files says so.

Main names. `behind_of_plan_trees_dense`.

By what. Each proof is the old proof with the twins' names in it.

Limits.
- These statements stand over Johnson/Prover/Link/FormFirst.lean, whose structure
  `TestFront` has the field `dense`. With a field `plain` in its stead, `testFront_of_dense`
   (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean), on which these statements rest, could
   not be proved.
- They do not reach the first chain's proximity test yet. The library proves the new hypothesis
  there, of the verifier's state (`taken_dense_entered`, Johnson/AtFull/Shape/TakenRowsDense.lean).
  These files do not show that the other hypotheses hold there: the other fields of `ShapeAsksD`
  (Johnson/Desc/ProofFile/Honest/K12/PlanBDense.lean), `planB`, and the hypotheses on the prover's
  data.
- `ShapeAsksD` is made from the old `ShapeAsks` (`shapeAsksD_of`), and so from the old mark
  `stPlainB`; and from `FrontAsksD`, the hypotheses on the front with the same new field, by
  `shapeAsksD_of_front` (ShapeAllDense.lean) and `shapeAsksD_of_two`, `shapeAsksD_of_form`,
  `shapeAsksD_of_draws` (ShapeOfTwoDense.lean); `FrontAsksD` is made by `frontAsksD_of_five`
  (FrontAtShapeDense.lean). These files lie in Johnson/Desc/ProofFile/Honest/K12/. Without a twin:
  `sorts_of_coreB` (SortsMember.lean) and `frontAsks_of_shape` (OneToAll.lean, not in the library
  yet).
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesPlan
import Johnson.Desc.ProofFile.Honest.K12.PlanBDense
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanLawDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody)
attribute [local instance] csNonempty
variable {W X : Type}

/-- The twin of `behind_of_plan_trees` (TreesPlan.lean), from `ShapeAsksD`. -/
theorem behind_of_plan_trees_dense (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsksD J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R)
    (a next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: nx' :: rest') (c : ℕ → GE) :
    BehindFirstT J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
      (J.trees₀ w fr C.mem (J.first w fr C)) D c := by
  obtain ⟨a', n', x', r', hst', hW⟩ := wanted_of_plan_dense J w fr C D K Dp cc R hP S F Dt c
  rw [hst] at hst'
  injection hst' with e1 e2
  injection e2 with e2 e3
  injection e3 with e3 e4
  subst e1 e2 e3 e4
  unfold Wanted at hW
  unfold BehindFirstT
  rw [← hst, Dt.trees]
  exact hW

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.behind_of_plan_trees_dense
