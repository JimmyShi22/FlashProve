-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ManyFitsAtDense.lean: the "dense" twin of `dataThree_of_front`
(ManyFitsAt.lean in this folder).

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

Main names. `dataThree_of_frontD`.

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
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12.Light
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes (Codes OracleNotice TableKey Group)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks)
open H2K.Member (piUFull)
open H2K.First (Plain gpOf logAt)
open Johnson.Prover.Link (batT)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (TestJob TestCoins FrontAsks frontFiveB stA ColsAt StateAt groupTrees)
open ProofFile.Honest.K12.Thin (thin_batT)
open ProofFile.Honest.Sh (testSh TestSh ThinSh thinSh batThin gpOfS gpOfS_eq plainSh claimsB)
variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The twin of `dataThree_of_front` (ManyFitsAt.lean), from `FrontAsksD`. The proof does not use
the field on the rows. -/
theorem dataThree_of_frontD (A : ManyJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (he : A.p.early = true) (h5 : frontFiveB A.p K (testSh (A.rec₀ w fr)) = true)
    (S : FrontAsksD A.toRun.toTest w fr K Dp)
    (hS : manyFitsS A.p (A.mems.map (·.shape)) A.trees
      (ProofFile.Honest.Sh.thinOf (testSh (A.rec₀ w fr))) = true) (C : TestCoins) :
    ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) ∧
      StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) ∧
      A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
        groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) := by
  unfold frontFiveB at h5
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h5
  obtain ⟨⟨⟨⟨-, -⟩, h4⟩, -⟩, -⟩ := h5
  rw [ProofFile.Honest.Sh.thinOf_eq] at hS
  have hp : (A.rec₀ w fr).pass = .nothing := by
    have h4' : (match ProofFile.Honest.Sh.passSh (A.rec₀ w fr).pass with
      | .nothing => true
      | _ => false) = true := h4
    cases hq : (A.rec₀ w fr).pass with
    | nothing => rfl
    | claim _ _ => rw [hq] at h4'; cases h4'
    | single _ _ => rw [hq] at h4'; cases h4'
    | switched _ _ _ => rw [hq] at h4'; cases h4'
  have hc : claimsB (A.rec₀ w fr) = true := S.claims
  unfold claimsB at hc
  cases hG : (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G =>
    exact dataThree_many A Dp (many_of_S A.p _ _ _ hp he hS G hG Dp (S.plain G hG).1) w fr C

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.dataThree_of_frontD
