-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the clause on the verifier's state, from what the rows say.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/AsksOmega.lean: under the head, at `jobAtOmega` at `doorOmegaF`, at every w, fr, C and every list that fits the test's rounds: `ShapeAsksO` with no premise on values, at one set of plain data with three trees, and `SaysAt` gives `DataAsks` there. The lines of `accepts_head_O`'s proof (K12/AtFile/OFields.lean), lifted, as K12/AsksWhole.lean's `asks_head` at the test on G_u.

  `onAsks_head_O`   **the statement**

Limits. True of the fall-back too if `SaysAt` holds there: no statement that the state on entry is the verifier's. `SaysAt` is a premise: at a run it is `says_head_O`'s, labelled «not in front of a law over coins»: that label goes with it. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendTable sendingPart witOf treesU columnOf readsBelow_mono
  jobOmega_readsBelow)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Own (K12AtO OldAtO fresh_tree_atOmega treeAt_own shapeAsks_of_front_own
  dataAsks_of_one_own dataThree_of_front_own accepts_of_plan_own pass_of_five)
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks noDigest)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St blocks first frontBlock)
open Desc.K14.Honest (Like)
open Johnson.G (proofSendsFull codesFull2)
open H2K.Member (piOFull)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (ManyJob jobAtOmega doorOmegaF colsOpened door_of_opened sentOf SaysAt
  bookCutsOmega askOf vecAt tsLenOf written_at_head qAt_written nums_head_O planOk_head_O shape_head_OmegaF
  colsMany plainMany rowsMu_many tree0_lent_head_Omega tree1_lent_head_Omega)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

set_option maxHeartbeats 1000000 in
/-- **`ShapeAsksO` at one set of plain data with three trees, under the head; and `SaysAt` gives `DataAsks` there.** -/
theorem onAsks_head_O {W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) :
    let A := jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
      (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols) weights rand omega?
    drawsFit (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds ds = true →
    ∃ Dp : H2K.First.Plain, Dp.ts.length = 3 ∧
      Own.ShapeAsksO A.toRun.toTest w fr C (byNo ds) codesFull2 Dp ∧
      (SaysAt A w fr C → ∃ (cc : ℕ → ℕ → List UInt64) (R : PlainRows),
        DataAsks A.toRun.toTest w fr C (byNo ds) Dp cc R) := by
  intro A hd
  obtain ⟨Dp, S⟩ := frontAsksO_head h hO bs hb A.toRun.toTest rfl key cols rfl w fr
  have he : A.p.early = true := H2K.JointK.early_of_planOk _ (planOk_head_O h hO)
  have hN : ProofFile.Honest.Sh.testSh (A.rec₀ w fr) = headShape Zp Np :=
    shape_head_OmegaF h bs hb key cols w fr
  have h5 : Own.frontOwnFiveB A.p codesFull2 (ProofFile.Honest.Sh.testSh (A.rec₀ w fr)) = true := by
    rw [hN]
    exact five_head_O h hO
  have hts : Dp.ts.length = 3 := by
    rw [ts_of_front_own A.toRun.toTest w fr codesFull2 Dp he h5 S]
    show tsLenOf pO (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (A.rec₀ w fr))) = 3
    rw [hN]
    exact ts_head_O h hO
  have hP : Own.planOB A.p codesFull2 Dp.ts.length = true := by
    rw [hts, ← ProofFile.Honest.K12.Light.codes_two]
    exact planOB_head_O h hO
  obtain ⟨a, next, rest, hs₀⟩ := stages_O
  have hst : A.toRun.toTest.p.nums.stages = a :: next :: rest := by
    show pO.nums.stages = _
    rw [nums_head_O h hO]
    exact hs₀
  have hd' : drawsFit ((H2K.JointK.laidOf A.p).map (·.1)) ds = true := by
    show drawsFit ((H2K.JointK.laidOf pO).map (·.1)) ds = true
    rw [laid_head_O h hO]
    exact hd
  have F := formAsks_of_draws A.toRun.toTest w fr C ds a next rest hst
    (formPub_of_B A.p a next rest hst (formPubB_head_O h hO)) hd'
  have SA := shapeAsks_of_front_own A.toRun.toTest w fr C (byNo ds) codesFull2 Dp hP S F
  have hS : ProofFile.Honest.K12.Light.manyFitsS A.p (A.mems.map (·.shape)) A.trees
      (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (A.rec₀ w fr))) = true := by
    rw [hN]
    exact many_head_O h hO _ weights rand omega?
  obtain ⟨t1, t2, t3⟩ := dataThree_of_front_own A w fr codesFull2 Dp he (pass_of_five _ _ _ h5) S hS C
  refine ⟨Dp, hts, SA, fun hs => ?_⟩
  have DF : DataFront A.toRun.toTest w fr C Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) :=
    ⟨t1, t2, t3, hs⟩
  exact ⟨_, _, dataAsks_of_one_own A.toRun.toTest w fr C (byNo ds) Dp _ _ S.door S.noMask S.tidy
    S.plainRows (bat_head_O h hO) F.bat DF⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.onAsks_head_O
