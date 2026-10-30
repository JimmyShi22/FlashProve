-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UAccepts.lean: at the key file's test on G_u the decision accepts
what the job's term shows, at every list of challenges that fits the declared rounds, where `SaysAt` holds.

  `plan_at_key`, `form_at_folded_test`, `shape_splits_at_key`   closed lines at the written place and sizes, by the kernel
  `three_at_folded_test`   the three tests on rows at the door's fall-back
  `LinesAt`        what the law asks of the parameters and the place: tests that read no input and no coin
  `front_of_lines`   `FrontAsks` at every input and front
  `accepts_of_lines`   the law, general in the parameters and the place
  `lines_at_key`, `eight_plan_at_key`   the tests hold at the written key's values

By what. `accepts_every_list` (K12/ShapeAll.lean), `frontAsks_all` (K12/FrontAtShape.lean),
`dataThree_of_front` (K12/ManyFitsAt.lean), `ts_of_front` (K12/AsksAtHead.lean), `shape_doorUF`,
`three_doorUF` (K12/DoorsByShape.lean), and the closed lines of E2E/KeyDoorUClosedKernel.lean.

Limits.
- `SaysAt` is a premise. The state on entry is the job's own, not shown here to be the verifier's.
- Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyDoorUClosedKernel
import E2E.KeyShapeSharedTies
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt
import Johnson.Desc.K12.Law.RoundsAtKeyPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.Light.KeyDoorUClosed
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn noDigest)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St blocks withU)
open H2K.Member (piKUFull)
open H2K.JointK (laidOf)
open AtPublicFiles.AtFiles.Full (QK)

/-- The plan's test at the written place, at two trees. By the kernel. -/
theorem plan_at_key : planB piKUFull QK.codes 2 = true := by decide +kernel

/-- Control: not at three trees. -/
theorem plan_at_key_bent : planB piKUFull QK.codes 3 = false := by decide +kernel

/-- Control: not at the other test's place. -/
theorem plan_at_key_place : planB H2K.Member.piKOFull QK.codes 2 = false := by decide +kernel

/-- Control: not at empty codes. -/
theorem plan_at_key_codes : planB piKUFull ⟨#[], #[]⟩ 2 = false := by decide +kernel

/-- The test on the place's public numbers. By the kernel. -/
theorem form_at_folded_test : formPubB piKUFull = true := by decide +kernel

/-- Control: not at a place with one stage. -/
theorem form_at_folded_test_bent : formPubB
    { piKUFull with nums := { piKUFull.nums with stages := piKUFull.nums.stages.take 1 } } = false := by
  decide +kernel

/-- The shared chain splits, and what goes out with o_u is there. By the kernel. -/
theorem shape_splits_at_key : QK.S.sharedSplitNeeded = true ∧ withU QK.S = some sentK := by decide +kernel

/-- The three tests on rows at the door's fall-back. -/
theorem three_at_folded_test : Three (fallU QK sentK) := by
  have h := three_U
  unfold threeL fallUK at h
  injection h with h1 h
  injection h with h2 h
  injection h with h3 _
  exact ⟨h1, h2, h3⟩

variable {W X : Type}

section
variable (Q : P14) (p : P12) (bs : List (Block St Unit)) (key : W → TableKey)
  (cols : W → Front X → List OpenedColumn) (weights : W → Weights) (rand : W → TableRand)
  (u? : Option (W → Front X → ℕ → OnBytes.E))

/-- What the law below asks of the parameters and the place: tests that read no input and no coin. -/
structure LinesAt : Prop where
  split : Q.S.sharedSplitNeeded = true
  goes : withU Q.S = some (sentOf Q.S)
  three : Three (fallU Q (sentOf Q.S))
  place : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true
  front : frontFiveB p Q.codes (Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf Q (sentOf Q.S))) = true
  many : manyFitsS p ((emptyU Q.codes Q.S).mems.map (·.shape)) (treesU p)
    (ProofFile.Honest.Sh.thinOf (Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf Q (sentOf Q.S)))) = true
  two : tsLenOf p (ProofFile.Honest.Sh.thinOf (Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf Q (sentOf Q.S)))) = 2
  plan : planB p Q.codes 2 = true
  form : formPubB p = true

variable {Q p bs}

/-- **`FrontAsks` at every input and front.** -/
theorem front_of_lines (L : LinesAt Q p) (hb : blocks Q = some bs) (hp : ∀ b ∈ bs, b.planOk = true)
    (J : TestJob W X) (hJp : J.p = p) (hJ : J.rec₀ = doorUF Q (sentOf Q.S) bs key cols) (w : W)
    (fr : Front X) : ∃ Dp : H2K.First.Plain, FrontAsks J w fr Q.codes Dp := by
  refine frontAsks_all J Q.codes (Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf Q (sentOf Q.S)))
    (by rw [hJp]; exact H2K.JointK.early_of_planOk _ L.place)
    (fun w fr => by rw [hJ]; exact shape_doorUF Q bs hb L.split _ L.goes key cols w fr)
    (by rw [hJp]; exact L.front) (fun w fr => ?_) w fr
  rw [hJ]
  have T := three_doorUF Q bs hb hp L.split _ L.goes L.three key cols w fr
  exact ⟨T.tidy, T.plain, T.claims⟩

/-- **The decision accepts what the term shows**, at every list that fits, where `SaysAt` holds. -/
theorem accepts_of_lines (L : LinesAt Q p) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (w : W) (fr : Front X) (C : TestCoins) (ds : List Fmt.Drawn)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds ds = true)
    (hs : SaysAt (jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?) w fr C) :
    ∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
      ((jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).rec₀ w fr)
      ((testAll (jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).toRun.toTest w fr C
        (byNo ds)).rs.map noDigest)
      (testAll (jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).toRun.toTest w fr C
        (byNo ds)).gs = .ok t' := by
  obtain ⟨Dp, S⟩ := front_of_lines key cols L hb hp
    (jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).toRun.toTest rfl rfl w fr
  have hN : ProofFile.Honest.Sh.testSh
      ((jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).rec₀ w fr) =
      Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf Q (sentOf Q.S)) :=
    shape_doorUF Q bs hb L.split _ L.goes key cols w fr
  have e1 : (jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).mems.map (·.shape) =
      (emptyU Q.codes Q.S).mems.map (·.shape) := shapes_plan_U Q 0 _ _ weights rand u?
  have e2 : (jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).trees = treesU p := rfl
  have hpA : (jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u?).p = p := rfl
  generalize jobAtU ⟨Q, 0⟩ p (doorUF Q (sentOf Q.S) bs key cols) weights rand u? = A
    at S hs hN e1 e2 hpA ⊢
  subst hpA
  have he : A.p.early = true := H2K.JointK.early_of_planOk _ L.place
  have h5 : frontFiveB A.p Q.codes (ProofFile.Honest.Sh.testSh (A.rec₀ w fr)) = true := by
    rw [hN]
    exact L.front
  have hM : manyFitsS A.p (A.mems.map (·.shape)) A.trees
      (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (A.rec₀ w fr))) = true := by
    rw [hN, e1, e2]
    exact L.many
  obtain ⟨t1, t2, t3⟩ := dataThree_of_front A w fr Q.codes Dp he h5 S hM C
  have hts : Dp.ts.length = 2 := by
    rw [ts_of_front A.toRun.toTest w fr Q.codes Dp he h5 S]
    show tsLenOf A.p (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (A.rec₀ w fr))) = 2
    rw [hN]
    exact L.two
  have hP : planB A.p Q.codes Dp.ts.length = true := by
    rw [hts]
    exact L.plan
  have hB : formPubB A.p = true := L.form
  have Dt : DataFront A.toRun.toTest w fr C Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) :=
    ⟨t1, t2, t3, hs⟩
  have hd' : drawsFit ((H2K.JointK.laidOf A.p).map (·.1)) ds = true := by
    rw [← H2K.Sw.k12_rounds guardedProximityTestParts A.p L.place]
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
      exact accepts_every_list A.toRun.toTest w fr C Q.codes Dp _ _ hP a next rest hst
        (formPub_of_B A.p a next rest hst hB) S Dt ds hd'

end

/-- **The tests hold at the written key's parameters and place.** -/
theorem lines_at_key : LinesAt QK piKUFull where
  split := shape_splits_at_key.1
  goes := shape_splits_at_key.2
  three := three_at_folded_test
  place := H2K.Pub.piKUFull_planOk
  front := front_U
  many := by
    have e : msU = (emptyU QK.codes QK.S).mems.map (·.shape) := by
      unfold msU bareU AQ
      exact shapes_plan_U QK 0 _ _ _ _ _
    have h := many_U
    rw [e] at h
    exact h
  two := ts_U
  plan := plan_at_key
  form := form_at_folded_test

/-- The eight plan, at the written key's parameters. -/
theorem eight_plan_at_key {bs : List (Block St Unit)} (hb : blocks QK = some bs) :
    ∀ b ∈ bs, b.planOk = true := by
  have h := plans_U
  unfold hpB at h
  rw [hb] at h
  exact fun b hb' => List.all_eq_true.1 h b hb'

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.plan_at_key
#print axioms ProofFile.Honest.K12.AtKey.plan_at_key_bent
#print axioms ProofFile.Honest.K12.AtKey.plan_at_key_place
#print axioms ProofFile.Honest.K12.AtKey.plan_at_key_codes
#print axioms ProofFile.Honest.K12.AtKey.form_at_folded_test
#print axioms ProofFile.Honest.K12.AtKey.form_at_folded_test_bent
#print axioms ProofFile.Honest.K12.AtKey.shape_splits_at_key
#print axioms ProofFile.Honest.K12.AtKey.three_at_folded_test
#print axioms ProofFile.Honest.K12.AtKey.front_of_lines
#print axioms ProofFile.Honest.K12.AtKey.accepts_of_lines
#print axioms ProofFile.Honest.K12.AtKey.lines_at_key
#print axioms ProofFile.Honest.K12.AtKey.eight_plan_at_key
