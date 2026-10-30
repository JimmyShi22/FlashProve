-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlanCausalDense.lean: the "dense" twin of `shapeAsks_congr`
(PlanCausal.lean in this folder).

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

Main names. `shapeAsksD_congr`.

By what. Each proof is the old proof with the twins' names in it. One line differs beyond that: the
new field is handed over in the old field's place.

Limits.
- These statements rest on this: in Johnson/Prover/Link/FormFirst.lean the structure
  `TestFront` has the field `dense`. With a field `plain` in its place,
  `testFront_of_dense` (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean), on which all the twins
  rest, could not be proved.
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
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanCausal
import Johnson.Desc.ProofFile.Honest.K12.PlanBDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
variable {W X : Type}
section
variable (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D D' : ℕ → Fmt.Drawn)
  (h : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) → D n = D' n)
include h

/-- The twin of `shapeAsks_congr` (PlanCausal.lean). The field `denseRows` names no challenge and
goes over as it stands. -/
theorem shapeAsksD_congr {K : Codes} {Dp : Plain} (S : ShapeAsksD J w fr C D K Dp) :
    ShapeAsksD J w fr C D' K Dp := by
  have e0 : D 0 = D' 0 := h 0 (by omega)
  have eT := tFold_congr J w fr C D D' h
  exact ⟨S.codes, S.door, S.came, S.tidy, S.denseRows, S.claims, by rw [← e0]; exact S.plain,
    by rw [← eT]; exact S.codes₁, by rw [← eT]; exact S.pub⟩

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.shapeAsksD_congr
