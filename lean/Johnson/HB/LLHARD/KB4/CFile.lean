-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CFile.lean: the named tests on the file at the full size's written values, as
far as Lean's kernel evaluates them: closed facts, list by list.

Main names.
  source_W: of sourceClauses' thirty the twenty-three that are carried (Slim.lean: maskS), at YW.
  shape_W: of shapeClauses' twelve the ten that are carried (maskH), at kW.
  plan_W: planClauses' nine, at kW and the written declared rounds' three lengths.
  front_W: the shared chain's front's six, at chainsW.
  stages_rng … k12_own: seven of the last twelve, at keyFull's values and the written places.
Negative tests. source_no, shape_no, plan_no, front_no: of each list ONE for the whole list, not one
a clause. Negative tests clause by clause, for the carried clauses of the first three lists:
Johnson/HB/LLHARD/KB9/SourceBent.lean, Johnson/HB/LLHARD/KB9/SourceBent2.lean,
Johnson/HB/LLHARD/KB9/ShapeBent.lean, Johnson/HB/LLHARD/KB9/PlanBent.lean. stages_no, stages_U_no,
stages_O_no, stages_own_no: a place's numbers against another test's stages. stages_idx_no,
stages_k_no, stages_code_no: one number moved each: a pair of codes' numbers, a stage's k, a code's
log-length. k12_no, k12_U_no, k12_O_no say no through proximityTestParametersAt's guard on the chain, not through
asksOnPlan's own questions; these four are bent one by one in k12_early_no, k12_answers_no,
k12_cut_no and k12_spend_no.
Limits. At written values alone. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.SourceW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

set_option maxRecDepth 1000000 in
theorem source_W : (patch maskS (sourceClauses YW)).all (·.2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With another number of answers as cut, the clause "cut" says no. -/
theorem source_no :
    (patch maskS (sourceClauses { YW with cutSamples := 2 })).all (·.2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem shape_W : (patch maskH (shapeClauses kW keyFull.once.shape)).all (·.2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the index-mask message under another mask code than the own group's, the fourth clause
says no. -/
theorem shape_no : (patch maskH (shapeClauses
    { kW with oneTime := { kW.oneTime with indexMasks := { kW.oneTime.indexMasks with
        shape := { kW.oneTime.indexMasks.shape with
          maskCode := kW.oneTime.indexMasks.shape.maskCode + 1 } } } }
    keyFull.once.shape)).all (·.2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem plan_W : (planClauses kW declKeyFull.1.length declKeyFull.2.1.length
    declKeyFull.2.2.length).all (·.2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With a round more taken of the third chain, the last but one clause says no. -/
theorem plan_no : (planClauses kW declKeyFull.1.length declKeyFull.2.1.length
    (declKeyFull.2.2.length + 1)).all (·.2) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem front_W : sharedFrontOk chainsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With the third chain's plan in the shared chain's stead as read back, the front says no. -/
theorem front_no : sharedFrontOk (chainsAt keyFull chainsW.made.key
    { kW with shared := { kW.shared with given := kW.second.given } }) = false := by
  decide +kernel

theorem stages_rng :
    stagesAsSized keyFull.codes keyFull.ranges.x.stages rangesNumsFull = true := by
  decide +kernel

theorem stages_U :
    stagesAsSized keyFull.codes keyFull.once.shape.testU laterPlacesFull.U = true := by
  decide +kernel

theorem stages_O : (match laterPlacesFull.O with
    | some nO => stagesAsSized keyFull.codes keyFull.once.shape.testOmega nO
    | none => keyFull.once.shape.testOmega.isEmpty) = true := by decide +kernel

theorem stages_own :
    stagesAsSized keyFull.codes keyFull.once.shape.testOwn laterPlacesFull.W = true := by
  decide +kernel

/-- The ranges' stages against the own test's place: no. -/
theorem stages_no :
    stagesAsSized keyFull.codes keyFull.ranges.x.stages laterPlacesFull.W = false := by
  decide +kernel

/-- One number moved: the first stage's pair of codes' numbers at the place. -/
theorem stages_idx_no : stagesAsSized keyFull.codes keyFull.ranges.x.stages
    { rangesNumsFull with idx := (0, 0) :: rangesNumsFull.idx.drop 1 } = false := by
  decide +kernel

/-- One number moved in the clause's substance: the first stage's k at the place. -/
theorem stages_k_no : stagesAsSized keyFull.codes keyFull.ranges.x.stages
    { rangesNumsFull with nums := { rangesNumsFull.nums with
        stages := match rangesNumsFull.nums.stages with
          | a :: l => { a with k := a.k + 1 } :: l
          | [] => [] } } = false := by
  decide +kernel

/-- One number moved: the first stage's main code's log-length at the place. -/
theorem stages_code_no : stagesAsSized keyFull.codes keyFull.ranges.x.stages
    { rangesNumsFull with nums := { rangesNumsFull.nums with
        stages := match rangesNumsFull.nums.stages with
          | a :: l => { a with C := { a.C with a := a.C.a + 1 } } :: l
          | [] => [] } } = false := by
  decide +kernel

/-- The folded row's stages against the own test's place: no. -/
theorem stages_U_no :
    stagesAsSized keyFull.codes keyFull.once.shape.testU laterPlacesFull.W = false := by
  decide +kernel

/-- Omega's stages against the folded row's test's place: no. -/
theorem stages_O_no :
    stagesAsSized keyFull.codes keyFull.once.shape.testOmega laterPlacesFull.U = false := by
  decide +kernel

/-- The own test's stages against the folded row's test's place: no. -/
theorem stages_own_no :
    stagesAsSized keyFull.codes keyFull.once.shape.testOwn laterPlacesFull.U = false := by
  decide +kernel

theorem k12_U : asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ laterPlacesFull.U) = true := by
  decide +kernel

theorem k12_O : (match laterPlacesFull.O with
    | some nO => asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
    | none => true) = true := by decide +kernel

theorem k12_own : asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ laterPlacesFull.W) = true := by
  decide +kernel

/-- At a place of another chain than the numbers': no. -/
theorem k12_no : asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 2, .K12⟩ laterPlacesFull.W) = false := by
  decide +kernel

/-- The folded row's test's numbers at a place of the third chain: no. -/
theorem k12_U_no : asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 9, .K12⟩ laterPlacesFull.U) = false := by
  decide +kernel

/-- Omega's test's numbers at a place of the third chain: no. -/
theorem k12_O_no : (match laterPlacesFull.O with
    | some nO => asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 10, .K12⟩ nO)
    | none => true) = false := by decide +kernel

/-! ### asksOnPlan's four questions, each bent alone, at the folded row's test's place -/

/-- The first question: the first fold's mask has come earlier. -/
theorem k12_early_no : asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩
    { laterPlacesFull.U with early := false }) = false := by decide +kernel

/-- The second: one answer to a sample. -/
theorem k12_answers_no : asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩
    { laterPlacesFull.U with answers := 2 }) = false := by decide +kernel

/-- The third, cutOk: the library's own two negative tests: the cut one round later, and one
earlier. -/
theorem k12_cut_no : (match (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ laterPlacesFull.U).nums.stages with
    | a :: _ =>
      (H2K.First.cutNo (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ laterPlacesFull.U) a (a.k + 1)).isEmpty ||
        (H2K.First.cutNo (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ laterPlacesFull.U) a (a.k - 1)).isEmpty
    | [] => true) = false := by decide +kernel

/-- The fourth, spendOk, which no other test asks: the library's own five negative tests
(H2K.Pub.spendSpoiled), at each of the four places: every one says no. -/
theorem k12_spend_no : ([H2U.proximityTestParametersAt ⟨1, none, 5, .K12⟩ rangesNumsFull,
    H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ laterPlacesFull.U,
    H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (laterPlacesFull.O.getD rangesNumsFull),
    H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ laterPlacesFull.W].any fun p =>
      (H2K.Pub.spendSpoiled p).any fun x => H2K.Pub.spendOk x.2) = false := by decide +kernel

/-- And at the four places themselves it says yes. -/
theorem k12_spend_yes : ([H2U.proximityTestParametersAt ⟨1, none, 5, .K12⟩ rangesNumsFull,
    H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ laterPlacesFull.U,
    H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (laterPlacesFull.O.getD rangesNumsFull),
    H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ laterPlacesFull.W].all H2K.Pub.spendOk) = true := by
  decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.source_W
#print axioms Johnson.KB4.source_no
#print axioms Johnson.KB4.shape_W
#print axioms Johnson.KB4.shape_no
#print axioms Johnson.KB4.plan_W
#print axioms Johnson.KB4.plan_no
#print axioms Johnson.KB4.front_W
#print axioms Johnson.KB4.front_no
#print axioms Johnson.KB4.stages_rng
#print axioms Johnson.KB4.stages_U
#print axioms Johnson.KB4.stages_O
#print axioms Johnson.KB4.stages_own
#print axioms Johnson.KB4.stages_no
#print axioms Johnson.KB4.k12_U
#print axioms Johnson.KB4.k12_O
#print axioms Johnson.KB4.k12_own
#print axioms Johnson.KB4.k12_no
#print axioms Johnson.KB4.stages_U_no
#print axioms Johnson.KB4.stages_O_no
#print axioms Johnson.KB4.stages_own_no
#print axioms Johnson.KB4.k12_U_no
#print axioms Johnson.KB4.k12_O_no
#print axioms Johnson.KB4.stages_idx_no
#print axioms Johnson.KB4.stages_k_no
#print axioms Johnson.KB4.stages_code_no
#print axioms Johnson.KB4.k12_early_no
#print axioms Johnson.KB4.k12_answers_no
#print axioms Johnson.KB4.k12_cut_no
#print axioms Johnson.KB4.k12_spend_no
#print axioms Johnson.KB4.k12_spend_yes
