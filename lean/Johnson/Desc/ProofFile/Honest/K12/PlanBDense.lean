-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlanBDense.lean: the "dense" twin of `ShapeAsks` (PlanB.lean in
this folder).

What it is. The old statements and structures hold or take `ShapeAsks` (PlanB.lean), whose field
`plainRows` asks that no open row and no sample row of the whole statement on entry has a
written-out variable (`stPlainB`, Johnson/Desc/Ground/Shape/Marks.lean). The twins hold or take
`ShapeAsksD` (PlanBDense.lean), which asks `DenseRow` of the rows taken in at the group under test.
`PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of a row has a written-out variable.
`DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables where every tensor is in order
and its slice lies inside its vector; it follows from `PlainRow` (`denseRow_of_plain`). The rows
meant are those that the proximity test takes in at the group under test (`runRows`,
OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each statement is the old
one, letter for letter.

Why. The only place where the old chain spends its hypothesis is the field `dense` of the library's
`TestFront`, which `testFront_of` fills from `PlainRow` by `denseRow_of_plain`. So the weaker
hypothesis is enough. That a row taken in at the first chain's proximity test has written-out
variables is read off the description's text; no theorem in these files says so.

Main names. `ShapeAsksD`, `shapeAsksD_of`.

By what. The structure is the old one but for the one field. `shapeAsksD_of`: `runRows_plain`
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean) and `denseRow_of_plain`.

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
import Johnson.Desc.ProofFile.Honest.K12.PlanB

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB)
variable {W X : Type}
section
variable (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)

/-- The twin of `ShapeAsks` (PlanB.lean). One field differs: in the place of `plainRows`, which asks
`stPlainB` of the whole statement on entry, stands `denseRows`, which asks `DenseRow` of the rows
taken in at the group under test. The state on entry is the job's, not shown to be the verifier's.

What the two fields on rows read. `tidy` speaks of the whole statement: of every group's open rows
and of every message's sample rows. Of each whole coefficient vector of a row (`Row.forms`) it asks
`Form.fits`, and so `Tensor.ok` of each tensor, whose third clause compares the pair of each
written-out variable with (1, 1); of a row's terms it reads the number of variables alone. Under
`stPlainB` that comparison was idle (Johnson/Desc/Ground/Shape/Marks.lean says so); here it is not.
`denseRows` speaks of the group under test alone, of terms too: every tensor is in order, which also
says that each written-out variable has the pair (1, 1), and its slice lies inside its vector, which
compares with the number of the vector's values. So neither field is a test on lists of numbers of
variables alone. Neither reads a row's target or an opened word. -/
structure ShapeAsksD (K : Codes) (Dp : Plain) : Prop where
  codes : (J.rec₀ w fr).st.codes = K
  door : Sh.doorB J.p (stA J.p) (stN J.p) (((laidOf J.p).take 1).map (·.1))
    (lettersOf J.p (stA J.p) (stN J.p)).i
    ((lettersOf J.p (stA J.p) (stN J.p)).n.code, (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode)
    (testSh (J.rec₀ w fr)) = true
  came : (J.rec₀ w fr).mask.isSome = true
  tidy : stTidyB (J.rec₀ w fr).st = true
  denseRows : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
    ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, DenseRow r
  claims : claimsB (J.rec₀ w fr) = true
  plain : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
    gpOf J.p (J.recB w fr (D 0)) (stA J.p) L = some Dp ∧ ok (gpL J.p (stA J.p) row Dp) = true ∧
      L.k = (sgOf (stA J.p)).h + (sgOf (stA J.p)).g ∧ L.h = (sgOf (stA J.p)).h ∧
      2 ^ L.logEll = (stA J.p).C.l ∧ 2 ^ L.logEllZk = (stA J.p).Z.l
  codes₁ : (tFold J w fr C D).st.codes = K
  pub : ∀ rows gp, (tFold J w fr C D).pass = .single rows gp →
    readPubB (coreSh ⟨(tFold J w fr C D).st, (tFold J w fr C D).book, (tFold J w fr C D).roots⟩)
      (singleSh rows) (stA J.p).C.a = true ∧
    OldOk (sgOf (stA J.p)) (sgOf (stN J.p)) (tFold J w fr C D).st.codes rows
      (lettersOf J.p (stA J.p) (stN J.p)).n.code (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode

/-- The old hypotheses give the new: a plain row is dense. -/
theorem shapeAsksD_of {K : Codes} {Dp : Plain} (S : ShapeAsks J w fr C D K Dp) :
    ShapeAsksD J w fr C D K Dp :=
  ⟨S.codes, S.door, S.came, S.tidy,
    fun _ hG r hr => denseRow_of_plain (runRows_plain S.plainRows hG r hr), S.claims, S.plain,
    S.codes₁, S.pub⟩

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.ShapeAsksD
#print axioms ProofFile.Honest.K12.shapeAsksD_of
