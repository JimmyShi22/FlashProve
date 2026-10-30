-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AsksAtHeadDense.lean: the "dense" twin of `ts_of_front`
(AsksAtHead.lean in this folder).

What it is. The old statements and structures hold, take or give `FrontAsks` (ShapeAll.lean) or
`ShapeAsks` (PlanB.lean), each with a field `plainRows`, which asks that no open row and no sample
row of the whole statement on entry has a written-out variable (`stPlainB`,
Johnson/Desc/Ground/Shape/Marks.lean). The twins have `FrontAsksD` (ShapeAllDense.lean) and
`ShapeAsksD` (PlanBDense.lean) in their places, whose field `denseRows` asks `DenseRow` of the rows
taken in at the group under test. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of a
row has a written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables
where every tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter. The files named here lie in
Johnson/Desc/ProofFile/Honest/K12/.

Why. Without these twins `ShapeAsksD` could be had from the old `ShapeAsks` alone, and so from the
old mark. These are the statements that make a `ShapeAsks` from tests on the front, and the second
member's condition at a play and at a run.

Main names. `ts_of_frontD`.

By what. Each twin's proof is the old proof with the twins' names in it.

Limits.
- These statements stand over Johnson/Prover/Link/FormFirst.lean, whose structure
  `TestFront` has the field `dense`, as all the twins do
  (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean says why).
- They do not reach the first chain's proximity test yet. The library proves the hypothesis on the
  rows there, of the verifier's state (`taken_dense_entered`,
  Johnson/AtFull/Shape/TakenRowsDense.lean). These files do not show the other hypotheses there: the
  tests on the front (`frontFiveB`), `stTidyB` and `claimsB` on entry, `planB`, and the hypotheses
  on the prover's data. `onFreeTD_at_run` (OnFreeTAtRunDense.lean) speaks of the shared chain, on
  which that test does not lie.
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Without a twin: `sorts_of_coreB` (SortsMember.lean), which makes a `ShapeAsks` from the test
  `coreB`, whose list has the clause `stPlainB`; `frontAsks_of_shape` (OneToAll.lean, not in the
  library), which no statement on the way to `OnFreeTD` calls; the forms without trees
  (`OnPlan`, `OnFree`, `AtEntry` and what is stated of them); the statements that conclude
  `ShapeAsks`, `FrontAsks` or `OnFreeT` at the shared chain's first test or at a small example:
  there the new conclusions follow from the old by `shapeAsksD_of`, `frontAsksD_of`, `onFreeTD_of`.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12.Light
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes (Codes OracleNotice TableKey Group)
open OnBytes.Params (IoppStage)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts stageAt Laid batAt foldAt switchAt)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks)
open H2K.Member (piUFull)
open H2K.JointK (laidOf laidS)
open H2K.First (Plain gpOf)
open Johnson.Prover.Link (stageOr swTarget swNotices stepPlanL stepPlanOk lastPlanL lastPlanOk
  dealtB declAt planFromOk batT asked)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (TestJob TestCoins FrontAsks ShapeAsks FormPub frontFiveB frontPlainB₀ stA stN
  lettersOf planB planL switchPlanB byNo shapeAsks_of_draws formPubB formPub_of_B planB_U_full)
open ProofFile.Honest.K12.Thin (thin_batT)
open ProofFile.Honest.Sh (testSh TestSh ThinSh thinSh batThin gpOfS gpOfS_eq plainSh switchPubB claimsB)
variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The twin of `ts_of_front` (AsksAtHead.lean), from `FrontAsksD`. The proof does not use the field
on the rows. -/
theorem ts_of_frontD (J : TestJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (he : J.p.early = true) (h : frontFiveB J.p K (testSh (J.rec₀ w fr)) = true)
    (S : FrontAsksD J w fr K Dp) :
    Dp.ts.length = tsLenOf J.p (ProofFile.Honest.Sh.thinOf (testSh (J.rec₀ w fr))) := by
  unfold frontFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, h4⟩, h5⟩, -⟩ := h
  rw [ProofFile.Honest.Sh.thinOf_eq] at h5 ⊢
  have hp : (J.rec₀ w fr).pass = .nothing := by
    have h4' : (match ProofFile.Honest.Sh.passSh (J.rec₀ w fr).pass with
      | .nothing => true
      | _ => false) = true := h4
    cases hq : (J.rec₀ w fr).pass with
    | nothing => rfl
    | claim _ _ => rw [hq] at h4'; cases h4'
    | single _ _ => rw [hq] at h4'; cases h4'
    | switched _ _ _ => rw [hq] at h4'; cases h4'
  have hc := S.claims
  unfold claimsB at hc
  cases hG : (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G => exact plain_ts J.p _ hp he h5 G hG Dp (S.plain G hG).1

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.ts_of_frontD
