-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OAccepts.lean: the decision of the key file's test on G_omega accepts what
the test shows, at every list that can be sampled, where `SaysAt` holds.

  `jobAtKey`                        the job at the written value and place, at any door's columns and readers
  `shape_at_key`, `three_at_key`    the state on entry has the one shape, and passes the three tests
  `plain_trees_of_front`            the number of the plain data's trees is read off the thin shape
  `frontAsks_at_key`                `FrontAsksO` at every input and front
  `accepts_at_key`                  the statement

Limits.
- `SaysAt` is a premise: what the rows taken in say of the words is not shown here.
- That the state on entry is the verifier's is not said: the door's fall-back passes these lines too.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OItems
import E2E.KeyDoorUClosedKernel
import Johnson.Desc.ProofFile.Honest.K12.Own.AcceptsOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.DataAsksOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.DataThreeOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.FrontOwnFive
import Johnson.Desc.ProofFile.Honest.K12.Own.PlanOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.ShapeAsksOwn
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.ProofFile.Honest.K12.FormDraws
import Johnson.Desc.K12.Law.RoundsAtKeyPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Codes TableKey Group)
open VerifiableInference.Desc (Block OpenedColumn noDigest)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks withU)
open H2K.Member (piKOFull piKUFull)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Own (FrontAsksO frontOwnFiveB frontAsksO_all pass_of_five shapeAsks_of_front_own
  dataAsks_of_one_own dataThree_of_front_own accepts_of_plan_own planOB planOB_KO_full)
open ProofFile.Honest.K12.Light (ManyJob jobAtOmega doorOmegaF SaysAt sentOf tsLenOf manyFitsS fallOmega
  shapes_plan_Omega plain_ts shape_doorOmegaF three_doorOmegaF Three colsMany plainMany noState)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeOm fallOm sentK AQ bareO msO hpB plans_U five_O ts_O many_O
  three_O threeL plan_U)
open ProofFile.Honest.Sh (TestSh testSh thinOf claimsB)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB)
open AtPublicFiles.AtFiles.Full (QK)

theorem split_at_key : QK.S.sharedSplitNeeded = true := by decide +kernel

theorem masks_ahead_at_key : QK.S.masksAhead = true := by decide +kernel

theorem lengths_at_key : QK.codes.lengthsOk = true := by decide +kernel

theorem sent_some_at_key : (withU QK.S).isSome = true := by decide +kernel

theorem sent_at_key : withU QK.S = some sentK := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 sent_some_at_key
  have e : sentK = v := by
    show (withU QK.S).getD #[] = v
    rw [hv]
    rfl
  rw [hv, e]

theorem plan_at_U : (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).planOk = true := by decide +kernel

theorem codes_at_key : QK.codes = H2K.Member.codesKeyFull := by decide +kernel

theorem eight_plans_at_key (bs : List (Block St Unit)) (hb : blocks QK = some bs) :
    ∀ b ∈ bs, b.planOk = true := by
  have h := plans_U
  unfold hpB at h
  rw [hb] at h
  exact List.all_eq_true.1 h

theorem three_at_fall : Three (fallOmega QK sentK piKUFull) := by
  have h : threeL fallOm = [true, true, true] := three_O
  unfold threeL at h
  simp only [List.cons.injEq, and_true] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

variable {W X : Type}

/-- **The job at the written value and place.** -/
abbrev jobAtKey (bs : List (Block St Unit)) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    ManyJob W X :=
  jobAtOmega AQ piKOFull (doorOmegaF QK sentK bs piKUFull key cols) weights rand omega?

/-- **The state on entry has the one shape.** -/
theorem shape_at_key (bs : List (Block St Unit)) (hb : blocks QK = some bs) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    testSh (doorOmegaF QK sentK bs piKUFull key cols w fr) = shapeOm :=
  shape_doorOmegaF QK bs hb split_at_key sentK sent_at_key piKUFull plan_at_U key cols w fr

/-- **The state on entry passes the three tests.** -/
theorem three_at_key (bs : List (Block St Unit)) (hb : blocks QK = some bs) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    Three (doorOmegaF QK sentK bs piKUFull key cols w fr) :=
  three_doorOmegaF QK bs hb (eight_plans_at_key bs hb) split_at_key masks_ahead_at_key sentK sent_at_key
    lengths_at_key piKUFull plan_at_U three_at_fall key cols w fr

/-- **The number of the plain data's trees is a function of the thin shape of the state in front.** -/
theorem plain_trees_of_front (J : TestJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : H2K.First.Plain)
    (he : J.p.early = true) (h : frontOwnFiveB J.p K (testSh (J.rec₀ w fr)) = true)
    (S : FrontAsksO J w fr K Dp) :
    Dp.ts.length = tsLenOf J.p (thinOf (testSh (J.rec₀ w fr))) := by
  have hp := pass_of_five _ _ _ h
  have hc : claimsB (J.rec₀ w fr) = true := S.claims
  unfold frontOwnFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, -⟩ := h
  rw [ProofFile.Honest.Sh.thinOf_eq] at h5 ⊢
  unfold claimsB at hc
  cases hG : (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G => exact plain_ts J.p _ hp he h5 G hG Dp (S.plain G hG).1

theorem early_at_key : piKOFull.early = true :=
  H2K.JointK.early_of_planOk _ H2K.Pub.piKOFull_planOk

/-- **`FrontAsksO` at every input and front**: there are plain data, which may hang on both. True of the
fall-back too: no statement that the state on entry is the verifier's. -/
theorem frontAsks_at_key (bs : List (Block St Unit)) (hb : blocks QK = some bs) (J : TestJob W X)
    (hp : J.p = piKOFull) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (hJ : J.rec₀ = doorOmegaF QK sentK bs piKUFull key cols) (w : W) (fr : Front X) :
    ∃ Dp, FrontAsksO J w fr QK.codes Dp :=
  frontAsksO_all J QK.codes shapeOm (by rw [hp]; exact early_at_key)
    (fun w fr => by rw [hJ]; exact shape_at_key bs hb key cols w fr)
    (by rw [hp]; exact five_O)
    (fun w fr => by
      rw [hJ]
      exact ⟨(three_at_key bs hb key cols w fr).tidy, (three_at_key bs hb key cols w fr).plain,
        (three_at_key bs hb key cols w fr).claims⟩) w fr

/-- **`manyFitsS` at every job at the written value and place.** -/
theorem many_at_key (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    manyFitsS piKOFull ((jobAtOmega AQ piKOFull door weights rand omega?).mems.map (·.shape))
      (jobAtOmega AQ piKOFull door weights rand omega?).trees (thinOf shapeOm) = true := by
  have e1 := shapes_plan_Omega QK 0 piKOFull door weights rand omega?
  have e2 := shapes_plan_Omega QK 0 piKOFull (fun (_ : Unit) (_ : Front Unit) => noState)
    (fun _ => ⟨fun _ _ => 0⟩) (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none
  have k := many_O
  have e3 : msO = (jobAtOmega AQ piKOFull (fun (_ : Unit) (_ : Front Unit) => noState)
    (fun _ => ⟨fun _ _ => 0⟩) (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none).mems.map (·.shape) := rfl
  have e4 : (jobAtOmega AQ piKOFull door weights rand omega?).mems.map (·.shape) = msO := by
    rw [e3]
    exact e1.trans e2.symm
  rw [e4]
  exact k

/-- **The decision accepts what the test shows**, at every list that can be sampled, where `SaysAt` holds. -/
theorem accepts_at_key (bs : List (Block St Unit)) (hb : blocks QK = some bs) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) :
    let A := jobAtKey bs key cols weights rand omega?
    drawsFit (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds ds = true →
    SaysAt A w fr C →
    ∃ t', (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).decide (A.toRun.toTest.rec₀ w fr)
      ((testAll A.toRun.toTest w fr C (byNo ds)).rs.map noDigest)
      (testAll A.toRun.toTest w fr C (byNo ds)).gs = .ok t' := by
  intro A hd hs
  obtain ⟨Dp, S⟩ := frontAsks_at_key bs hb A.toRun.toTest rfl key cols rfl w fr
  have he : A.p.early = true := early_at_key
  have hN : testSh (A.rec₀ w fr) = shapeOm := shape_at_key bs hb key cols w fr
  have h5 : frontOwnFiveB A.p QK.codes (testSh (A.rec₀ w fr)) = true := by
    rw [hN]
    exact five_O
  have hts : Dp.ts.length = 3 := by
    rw [plain_trees_of_front A.toRun.toTest w fr QK.codes Dp he h5 S]
    show tsLenOf piKOFull (thinOf (testSh (A.rec₀ w fr))) = 3
    rw [hN]
    exact ts_O
  have hP : planOB A.p QK.codes Dp.ts.length = true := by
    rw [hts, codes_at_key]
    exact planOB_KO_full
  obtain ⟨a, next, rest, hs₀⟩ : ∃ a next rest, piKOFull.nums.stages = a :: next :: rest :=
    ⟨_, _, _, rfl⟩
  have hst : A.toRun.toTest.p.nums.stages = a :: next :: rest := hs₀
  have hd' : drawsFit ((H2K.JointK.laidOf A.p).map (·.1)) ds = true := by
    have e : (H2K.JointK.laidOf A.p).map (·.1) = (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds :=
      (H2K.Sw.k12_rounds guardedProximityTestParts piKOFull H2K.Pub.piKOFull_planOk).symm
    rw [e]
    exact hd
  have F := formAsks_of_draws A.toRun.toTest w fr C ds a next rest hst
    (formPub_of_B A.p a next rest hst form_at_key) hd'
  have SA := shapeAsks_of_front_own A.toRun.toTest w fr C (byNo ds) QK.codes Dp hP S F
  have hS : manyFitsS A.p (A.mems.map (·.shape)) A.trees (thinOf (testSh (A.rec₀ w fr))) = true := by
    rw [hN]
    exact many_at_key _ weights rand omega?
  obtain ⟨t1, t2, t3⟩ := dataThree_of_front_own A w fr QK.codes Dp he (pass_of_five _ _ _ h5) S hS C
  have DF : DataFront A.toRun.toTest w fr C Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) :=
    ⟨t1, t2, t3, hs⟩
  have Dt := dataAsks_of_one_own A.toRun.toTest w fr C (byNo ds) Dp _ _ S.door S.noMask S.tidy
    S.plainRows cut_at_key F.bat DF
  exact accepts_of_plan_own A.toRun.toTest w fr C (byNo ds) QK.codes Dp _ _ own_mask_at_key hP SA F Dt

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.sent_at_key
#print axioms ProofFile.Honest.K12.AtKey.eight_plans_at_key
#print axioms ProofFile.Honest.K12.AtKey.shape_at_key
#print axioms ProofFile.Honest.K12.AtKey.three_at_key
#print axioms ProofFile.Honest.K12.AtKey.plain_trees_of_front
#print axioms ProofFile.Honest.K12.AtKey.frontAsks_at_key
#print axioms ProofFile.Honest.K12.AtKey.many_at_key
#print axioms ProofFile.Honest.K12.AtKey.accepts_at_key
