-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/AcceptedAtU.lean: the field `accepts` of `K12At` at the test on G_u, and
the job at the seated place. `AcceptedHead.lean` puts the five fields together.

  `laid_written_U`, `laid_head_U`   the declared rounds of `laidOf` are the block's
  `accepts_head_U`   the decision accepts what the term shows, at every list that can be sampled, where
                 `SaysAt` holds: `accepts_every_list` (K12/ShapeAll.lean) at `frontAsks_head`,
                 `dataThree_head` (K12/ManyFitsAt.lean), `planB_head`, `formPubB_head` (K12/AsksAtHead.lean)
  `stages_len`, `stages_head_U`   the place has five stages

Limits.
- `SaysAt` is a premise: `says_head_U` (AcceptedAtNine.lean) pays it at a stand.
- AT THE FILLING, NOT READ THROUGH: a half read through a reader of the coins is no `proverSideOfProximityTest`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesSentBeforeTestAtU
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtTest
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import AtFullSide.K12.CutsAtHead
import AtFullSide.K12.LaterJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace treesU)
open ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place OpenedColumn noDigest)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks frontBlock withU first)
open Desc.K14.Honest (Like)
open Johnson.G (proofSendsFull codesFull2)

open H2K.Member (piUFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (jobAtU doorUF colsLoc sentOf SaysAt bookCutsU dataThree_head shape_head_UF
  five_head ts_head planB_head formPubB_head ts_of_front colsMany plainMany alike_head_U
  planOk_head_U ManyJob)

/-- The declared rounds at the written place. By the kernel. -/
theorem laid_written_U : (H2K.JointK.laidOf piUFull).map (·.1) = (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem laid_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    (H2K.JointK.laidOf (fourOf Np).U).map (·.1) = (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).rounds := by
  rw [(alike_head_U h).decls, rounds_head_U h]
  exact laid_written_U

/-- **The decision accepts what the term shows**, at every list that can be sampled, where `SaysAt`
holds. -/
theorem accepts_head_U {W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (C : TestCoins) (ds : List Fmt.Drawn) :
    let A := jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U
      (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs key cols) weights rand u?
    drawsFit (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds ds = true →
    SaysAt A w fr C →
    ∃ t', (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).decide (A.toRun.toTest.rec₀ w fr)
      ((testAll A.toRun.toTest w fr C (byNo ds)).rs.map noDigest)
      (testAll A.toRun.toTest w fr C (byNo ds)).gs = .ok t' := by
  intro A hd hs
  obtain ⟨Dp, S, T⟩ := dataThree_head h bs hb key cols weights rand u? w fr
  obtain ⟨t1, t2, t3⟩ := T C
  have he : A.p.early = true := H2K.JointK.early_of_planOk _ (planOk_head_U h)
  have hN : ProofFile.Honest.Sh.testSh (A.rec₀ w fr) =
      Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) :=
    shape_head_UF h bs hb key cols w fr
  have h5 : frontFiveB A.p codesFull2 (ProofFile.Honest.Sh.testSh (A.rec₀ w fr)) = true := by
    rw [hN]
    exact five_head h
  have hts : Dp.ts.length = 2 := by
    rw [ts_of_front A.toRun.toTest w fr codesFull2 Dp he h5 S]
    show ProofFile.Honest.K12.Light.tsLenOf (fourOf Np).U
      (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (A.rec₀ w fr))) = 2
    rw [hN]
    exact ts_head h
  have hB : formPubB A.p = true := formPubB_head h
  have hP : planB A.p codesFull2 Dp.ts.length = true := by
    rw [hts]
    exact planB_head h
  have Dt : DataFront A.toRun.toTest w fr C Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) :=
    ⟨t1, t2, t3, hs⟩
  have hd' : drawsFit ((H2K.JointK.laidOf A.p).map (·.1)) ds = true := by
    show drawsFit ((H2K.JointK.laidOf (fourOf Np).U).map (·.1)) ds = true
    rw [laid_head_U h]
    exact hd
  cases hst : A.p.nums.stages with
  | nil =>
    unfold formPubB at hB
    rw [hst] at hB
    cases hB
  | cons a l1 =>
    cases l1 with
    | nil =>
      unfold formPubB at hB
      rw [hst] at hB
      cases hB
    | cons next rest =>
      exact accepts_every_list A.toRun.toTest w fr C codesFull2 Dp _ _ hP a next rest hst
        (formPub_of_B A.p a next rest hst hB) S Dt ds hd'

/-- The written place has five stages. By the kernel. -/
theorem stages_len : piUFull.nums.stages.length = 5 := by decide +kernel

/-- The seated place has two stages or more. -/
theorem stages_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ a b l, (fourOf Np).U.nums.stages = a :: b :: l := by
  have hl : (fourOf Np).U.nums.stages.length = 5 := by
    rw [ProofFile.Honest.K12.Light.nums_head_U h]
    exact stages_len
  cases hh : (fourOf Np).U.nums.stages with
  | nil =>
    rw [hh] at hl
    cases hl
  | cons a l₁ =>
    cases l₁ with
    | nil =>
      rw [hh] at hl
      cases hl
    | cons b l => exact ⟨a, b, l, rfl⟩

section
variable {W₀ Rc X₀ Cl V Pb : Type} {Bk : ProverCoinCounts}


end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.stages_len
#print axioms ProofFile.Honest.K12.AtFile.stages_head_U
#print axioms ProofFile.Honest.K12.AtFile.laid_written_U
#print axioms ProofFile.Honest.K12.AtFile.laid_head_U
#print axioms ProofFile.Honest.K12.AtFile.accepts_head_U
