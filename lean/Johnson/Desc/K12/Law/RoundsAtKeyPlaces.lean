-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RoundsAtKeyPlaces.lean: the condition of the law of a proximity test (the kind
K12), `K12Condition`, with no premise, and "every written round is below, "BAT" included", at the
three later places of the key file at the full size. Statements and proofs: a file of calls and of
closed lines that the kernel evaluates. It is Johnson/Desc/K12/Law/CondMembersFull.lean and
RoundsAtPlaces.lean (the proof file's four places), place for place.

Why. The comparisons lie in the library: `tests_ok` (Johnson/Bridge/TestsAtWritten.lean) holds
every count of every fold, switch and last stage of the nine written tests at the full size against
2^-128, by the kernel; the key file's and the entry file's five stand first in that list. Here the
key file gets the tie of a written test to a place, the tests on the plan at the place,
and the round "BAT", which stands in front of the chain and in no written test.
Main names; ‹X› is KU (the folded row, ⟨2, none, 9, .K12⟩), KO (Omega, ⟨2, none, 10, .K12⟩), KW (the
own test, ⟨3, none, 2, .K12⟩).
  `held_‹X›`: seven fields of the closed place (stages, rows, work, own mask, the codes' numbers,
    answers, early) are what the library's typed sizes of a key (`Lk6.AtPlan.keyFull`,
    Johnson/Goal/PlanValues/KeySizedReturns.lean) and the typed setting (`setAt`) give by the text
    of `Key.laterPlaces`: the right sides are those of `later_of_full`
    (Johnson/Desc/K12/Law/Sizes/KeyAtScope.lean [not imported]), to the letter.
    `radii_‹X›`: the closed radii are `radiusOf setAt` at the typed stages. `codes_held`: the closed
    table of codes is the typed sizes'. For these no print is trusted.
  `trial_‹X›`: the written test number 1, 2 or 3 of the nine is the test of the place's stages at 32
    bits of work.
  `pi‹X›Full_planOk`, `_pubOk`, `_johOk`, `_bat` (`batPriceOk` at 128), `_v0`, `_works`, `_rad`.
  `k12Condition_pi‹X›Full`, `k12Condition_pi‹X›Full_r`: the condition at the written test's radii;
    at the closed radii.
  `roundsBelow_pi‹X›Full`: `RoundsBelow` at 2^-128. `roundsHold_pi‹X›Full`,
    `roundsBelowAt_pi‹X›Full`: the stronger form, with the radii pinned from both sides
    (`RoundsHoldAt`, Johnson/Desc/K12/Law/RoundsHold.lean), and the form with the radii as a
    function of the stage in the library's form (`RoundsBelowAt`, RoundsAtMade.lean).
    `pi‹X›Full_batPlace`, `_pay`. `T‹X›Full`, `closed_‹X›Full`: the trees in front of the stretch,
    by source, with their depths; and `Closed` (Johnson/Desc/K12/Coin/LawAt.lean) at the place: the
    test on the plan, the condition, `placeOk`, `johOk`, `batPriceOk`: what a caller of the law at a
    closed place lays; its lighter form is `Closed.light` (LawAtLight.lean). `place_teeth`: six
    plans of trees at which `placeOk` says no.
  `opens_‹X›`: the declared openings of the first switch: label and source, written out.
    `labelTests_‹X›`: what the two tests on labels say there (`ownLabelsFreeB`,
    Johnson/Desc/K12/Coin/GameAt.lean; `ownLabelsB`, FirstBook.lean): both yes at KU; no and yes at
    KO; both no at KW, whose openings are all of trees of the two chains in front.
It stands over files of Johnson/Bridge/, and so over Cb/Bridge/CodeListRSProved.lean and
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15). It takes no run of their text; it calls their names.
Limits. Four numbers of each closed place are a print's word: they hang on the plans and the
sendings, not on the sizes: the first switch's declared openings (`first`), the first free own
number (`free`), the first tree's number (`firstTree`), and the number of the first group, which is
no field of a place: it enters through the list `oracles`. By a reading of `H2U.proximityTestParametersAt`
(Johnson/Desc/K12/AtPlan.lean) the lists `oracles` and `before` are computed from these; no theorem
here says so. The three tables of trees `T‹X›Full` were typed by hand after these fields: they too
are a print's word. That a description makes these places at any public files is not said here. The
limits of the condition stand: one round's share of its written verifier messages, bits of work
among them: 32 of the 128 bits are work at "CS" and "BASE"; no sum over rounds. "BAT" stands in
front of the chain and is not in the condition: here its number is priced alone; the law that this
number bounds the round's bad verifier messages is the game's (`bat_vals_yOf_rows`,
Johnson/Desc/K12/Law/TupleVals.lean; spent in `k12_lawRec`, Johnson/Desc/K12/Coin/PaidRec.lean) and
is not called here. The key file's fourth place (the ranges' test) is not here. No soundness is
claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.RoundsHoldPlaces
import Johnson.Desc.K12.Law.PlacesKeyFull
import Johnson.Desc.K12.Law.Sizes.StagesFull
import Johnson.Desc.K12.Plan.PlaceOfPlan
import Johnson.Desc.K12.Coin.GameAt
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.K12.Coin.LawAtLight
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (TestAt testsFull)
open Johnson.Top.H (radiusOf)
open H2K.Member (piKUFull piKOFull piKWFull codesKeyFull rKUFull rKOFull rKWFull setAt)
open scoped ENNReal

/-- The closed table of codes is the typed sizes': by the kernel. -/
theorem codes_held : codesKeyFull = Lk6.AtPlan.keyFull.codes := by decide +kernel

/-! ## The folded row -/

/-- Seven fields of the closed place are what the typed sizes of a key and the typed setting give by
the text of `Key.laterPlaces`: by the kernel. No print is trusted for these. -/
theorem held_KU :
    piKUFull.nums.stages = Lk6.AtPlan.keyFull.once.folded.stages.map H2U.stageNums ∧
      piKUFull.nums.rows = Lk6.AtPlan.keyFull.once.shape.fold.index.answers +
        Lk6.AtPlan.keyFull.once.shape.fold.columns + 1 + 2 * setAt.samples ∧
      piKUFull.nums.work = setAt.workOf .query
        (if Lk6.AtPlan.keyFull.once.lines.oneTime then .once else .shared) ∧
      piKUFull.nums.ownMask = !Lk6.AtPlan.keyFull.once.shape.masksAhead ∧
      piKUFull.idx = Lk6.AtPlan.keyFull.once.shape.testU.map (fun s => (s.code, s.maskCode)) ∧
      piKUFull.answers = setAt.samples ∧
      piKUFull.early = Lk6.AtPlan.keyFull.once.shape.choice.masksRide := by decide +kernel

/-- The closed radii are the planner's, at the typed sizes' stages: by the kernel. -/
theorem radii_KU : Lk6.AtPlan.keyFull.once.folded.stages.map (fun y => radiusOf setAt y.g) =
    Lk6.AtPlan.keyFull.once.folded.stages.map (fun y => rKUFull (H2U.stageNums y)) :=
        by decide +kernel

/-- The written test number 1 of the nine IS the test of the place's stages and work. -/
theorem trial_KU : Trial testsFull 1 piKUFull.nums.stages 32 := ⟨_, rfl, rfl⟩

theorem piKUFull_planOk : (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).planOk = true :=
    by decide +kernel

theorem piKUFull_pubOk : pubOk piKUFull codesKeyFull = true := by decide +kernel

theorem piKUFull_johOk : johOk piKUFull rKUFull = true := by decide +kernel

theorem piKUFull_bat : batPriceOk piKUFull rKUFull 128 = true := by decide +kernel

theorem piKUFull_v0 : batV0 piKUFull rKUFull = 5915 := by decide +kernel

theorem piKUFull_works :
    workRounds piKUFull = [("CS", 32), ("CS", 32), ("CS", 32), ("CS", 32), ("BASE", 32)] := by
  decide +kernel

/-- **A member**: the condition at the place, with no premise. -/
theorem k12Condition_piKUFull : ∃ T, testsFull[1]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piKUFull codesKeyFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsFull (fun _ h => ok_full h) 1 piKUFull.nums.stages 32 trial_KU
    piKUFull codesKeyFull rfl rfl piKUFull_planOk piKUFull_pubOk

theorem piKUFull_rad : ∀ a ∈ piKUFull.nums.stages,
    radOf (testNo testsFull 1) (sgOf a) = rKUFull (sgOf a).st := by decide +kernel

/-- The same at the closed radii. -/
theorem k12Condition_piKUFull_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rKUFull s.st) piKUFull codesKeyFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piKUFull
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piKUFull_rad hK

/-- **Every written round of the place's test, "BAT" included, is below.** -/
theorem roundsBelow_piKUFull : RoundsBelow piKUFull rKUFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piKUFull_r piKUFull_bat

theorem piKUFull_batPlace : batPlaceB piKUFull (fun s => rKUFull s.st) = true := by decide +kernel

theorem piKUFull_pay : batPayOk piKUFull rKUFull 128 = true := by decide +kernel

/-- **Every written round is below, with the radii pinned from both sides.** -/
theorem roundsHold_piKUFull :
    RoundsHoldAt piKUFull (fun s => rKUFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piKUFull_r piKUFull_batPlace

/-- The form with the radii as a function of the stage in the library's form. -/
theorem roundsBelowAt_piKUFull :
    RoundsBelowAt piKUFull (fun s => rKUFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piKUFull.below

/-! ## Omega -/

/-- Seven fields of the closed place are what the typed sizes of a key and the typed setting give by
the text of `Key.laterPlaces`: by the kernel. No print is trusted for these. -/
theorem held_KO :
    piKOFull.nums.stages = Lk6.AtPlan.keyFull.once.omega.stages.map H2U.stageNums ∧
      piKOFull.nums.rows = 1 + 2 * setAt.samples ∧
      piKOFull.nums.work = setAt.workOf .query
        (if Lk6.AtPlan.keyFull.once.lines.oneTime then .once else .shared) ∧
      piKOFull.nums.ownMask = true ∧
      piKOFull.idx = Lk6.AtPlan.keyFull.once.shape.testOmega.map (fun s => (s.code, s.maskCode)) ∧
      piKOFull.answers = setAt.samples ∧
      piKOFull.early = Lk6.AtPlan.keyFull.once.shape.choice.masksRide := by decide +kernel

/-- The closed radii are the planner's, at the typed sizes' stages: by the kernel. -/
theorem radii_KO : Lk6.AtPlan.keyFull.once.omega.stages.map (fun y => radiusOf setAt y.g) =
    Lk6.AtPlan.keyFull.once.omega.stages.map (fun y => rKOFull (H2U.stageNums y)) :=
        by decide +kernel

/-- The written test number 2 of the nine IS the test of the place's stages and work. -/
theorem trial_KO : Trial testsFull 2 piKOFull.nums.stages 32 := ⟨_, rfl, rfl⟩

theorem piKOFull_planOk : (proximityTestKind guardedProximityTestParts piKOFull : Block T12 Unit).planOk = true :=
    by decide +kernel

theorem piKOFull_pubOk : pubOk piKOFull codesKeyFull = true := by decide +kernel

theorem piKOFull_johOk : johOk piKOFull rKOFull = true := by decide +kernel

theorem piKOFull_bat : batPriceOk piKOFull rKOFull 128 = true := by decide +kernel

theorem piKOFull_v0 : batV0 piKOFull rKOFull = 476 := by decide +kernel

theorem piKOFull_works :
    workRounds piKOFull = [("CS", 32), ("CS", 32), ("CS", 32), ("BASE", 32)] := by
  decide +kernel

/-- **A member**: the condition at the place, with no premise. -/
theorem k12Condition_piKOFull : ∃ T, testsFull[2]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piKOFull codesKeyFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsFull (fun _ h => ok_full h) 2 piKOFull.nums.stages 32 trial_KO
    piKOFull codesKeyFull rfl rfl piKOFull_planOk piKOFull_pubOk

theorem piKOFull_rad : ∀ a ∈ piKOFull.nums.stages,
    radOf (testNo testsFull 2) (sgOf a) = rKOFull (sgOf a).st := by decide +kernel

/-- The same at the closed radii. -/
theorem k12Condition_piKOFull_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rKOFull s.st) piKOFull codesKeyFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piKOFull
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piKOFull_rad hK

/-- **Every written round of the place's test, "BAT" included, is below.** -/
theorem roundsBelow_piKOFull : RoundsBelow piKOFull rKOFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piKOFull_r piKOFull_bat

theorem piKOFull_batPlace : batPlaceB piKOFull (fun s => rKOFull s.st) = true := by decide +kernel

theorem piKOFull_pay : batPayOk piKOFull rKOFull 128 = true := by decide +kernel

/-- **Every written round is below, with the radii pinned from both sides.** -/
theorem roundsHold_piKOFull :
    RoundsHoldAt piKOFull (fun s => rKOFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piKOFull_r piKOFull_batPlace

/-- The form with the radii as a function of the stage in the library's form. -/
theorem roundsBelowAt_piKOFull :
    RoundsBelowAt piKOFull (fun s => rKOFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piKOFull.below

/-! ## The own test -/

/-- Seven fields of the closed place are what the typed sizes of a key and the typed setting give by
the text of `Key.laterPlaces`: by the kernel. No print is trusted for these. -/
theorem held_KW :
    piKWFull.nums.stages = Lk6.AtPlan.keyFull.once.own.stages.map H2U.stageNums ∧
      piKWFull.nums.rows = 2 + 3 * setAt.samples ∧
      piKWFull.nums.work = setAt.workOf .query
        (if Lk6.AtPlan.keyFull.once.lines.oneTime then .once else .request) ∧
      piKWFull.nums.ownMask = !Lk6.AtPlan.keyFull.once.shape.masksAhead ∧
      piKWFull.idx = Lk6.AtPlan.keyFull.once.shape.testOwn.map (fun s => (s.code, s.maskCode)) ∧
      piKWFull.answers = setAt.samples ∧
      piKWFull.early = Lk6.AtPlan.keyFull.once.shape.choice.masksRide := by decide +kernel

/-- The closed radii are the planner's, at the typed sizes' stages: by the kernel. -/
theorem radii_KW : Lk6.AtPlan.keyFull.once.own.stages.map (fun y => radiusOf setAt y.g) =
    Lk6.AtPlan.keyFull.once.own.stages.map (fun y => rKWFull (H2U.stageNums y)) := by decide +kernel

/-- The written test number 3 of the nine IS the test of the place's stages and work. -/
theorem trial_KW : Trial testsFull 3 piKWFull.nums.stages 32 := ⟨_, rfl, rfl⟩

theorem piKWFull_planOk : (proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).planOk = true :=
    by decide +kernel

theorem piKWFull_pubOk : pubOk piKWFull codesKeyFull = true := by decide +kernel

theorem piKWFull_johOk : johOk piKWFull rKWFull = true := by decide +kernel

theorem piKWFull_bat : batPriceOk piKWFull rKWFull 128 = true := by decide +kernel

theorem piKWFull_v0 : batV0 piKWFull rKWFull = 952 := by decide +kernel

theorem piKWFull_works :
    workRounds piKWFull = [("CS", 32), ("CS", 32), ("CS", 32), ("CS", 32), ("BASE", 32)] := by
  decide +kernel

/-- **A member**: the condition at the place, with no premise. -/
theorem k12Condition_piKWFull : ∃ T, testsFull[3]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piKWFull codesKeyFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsFull (fun _ h => ok_full h) 3 piKWFull.nums.stages 32 trial_KW
    piKWFull codesKeyFull rfl rfl piKWFull_planOk piKWFull_pubOk

theorem piKWFull_rad : ∀ a ∈ piKWFull.nums.stages,
    radOf (testNo testsFull 3) (sgOf a) = rKWFull (sgOf a).st := by decide +kernel

/-- The same at the closed radii. -/
theorem k12Condition_piKWFull_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rKWFull s.st) piKWFull codesKeyFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piKWFull
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piKWFull_rad hK

/-- **Every written round of the place's test, "BAT" included, is below.** -/
theorem roundsBelow_piKWFull : RoundsBelow piKWFull rKWFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piKWFull_r piKWFull_bat

theorem piKWFull_batPlace : batPlaceB piKWFull (fun s => rKWFull s.st) = true := by decide +kernel

theorem piKWFull_pay : batPayOk piKWFull rKWFull 128 = true := by decide +kernel

/-- **Every written round is below, with the radii pinned from both sides.** -/
theorem roundsHold_piKWFull :
    RoundsHoldAt piKWFull (fun s => rKWFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piKWFull_r piKWFull_batPlace

/-- The form with the radii as a function of the stage in the library's form. -/
theorem roundsBelowAt_piKWFull :
    RoundsBelowAt piKWFull (fun s => rKWFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piKWFull.below

/-! ## The first switch's declared openings, and the two tests on labels -/

/-- Label and source of each declared opening of a place's first switch. -/
def opensAt (π : P12) : List (Nat × Fmt.TreeSource) :=
  match π.nums.stages with
  | a :: _ => (H2K.First.opensOf π a.k).map fun o => (o.1.tree, o.2)
  | [] => []

theorem opens_KU : opensAt piKUFull = [(0, .own 0), (2, .own 2)] := by decide +kernel

theorem opens_KO : opensAt piKOFull = [(1, .own 1), (2, .own 2), (7, .own 7)] := by decide +kernel

theorem opens_KW : opensAt piKWFull = [(0, .taken 0 0), (5, .taken 0 5), (1, .taken 1 1)] := by
  decide +kernel

theorem labelTests_KU : Coin.ownLabelsFreeB piKUFull = true ∧ Coin.ownLabelsB piKUFull = true := by
  decide +kernel

/-- At Omega the last opening is the own tree number 7, and 7 is the first free own number: the test
that asks "in front of the test" says no. -/
theorem labelTests_KO : Coin.ownLabelsFreeB piKOFull = false ∧ Coin.ownLabelsB piKOFull = true := by
  decide +kernel

theorem labelTests_KW :
    Coin.ownLabelsFreeB piKWFull = false ∧ Coin.ownLabelsB piKWFull = false := by
  decide +kernel

/-! ## The law's public premises, closed -/

/-- The trees in front of the stretch at the folded row, by source, with their depths. -/
def TKUFull : List (Fmt.TreeSource × ℕ) :=
  [(.own 0, 24), (.own 1, 22), (.own 2, 13)]

/-- At Omega: these, and the four that the folded row's test sends. -/
def TKOFull : List (Fmt.TreeSource × ℕ) :=
  [(.own 0, 24), (.own 1, 22), (.own 2, 13), (.own 3, 21), (.own 4, 17), (.own 5, 13), (.own 6, 14)]

/-- At the own test: three trees of the two chains in front. -/
def TKWFull : List (Fmt.TreeSource × ℕ) :=
  [(.taken 0 0, 13), (.taken 0 5, 22), (.taken 1 1, 22)]

/-- **Four tests with code and the condition**, at the folded row. -/
theorem closed_KUFull : Coin.Closed piKUFull rKUFull codesKeyFull 1 0 0 TKUFull :=
  ⟨piKUFull_planOk, k12Condition_piKUFull_r, by decide +kernel, piKUFull_johOk, piKUFull_bat⟩

theorem closed_KOFull : Coin.Closed piKOFull rKOFull codesKeyFull 1 0 0 TKOFull :=
  ⟨piKOFull_planOk, k12Condition_piKOFull_r, by decide +kernel, piKOFull_johOk, piKOFull_bat⟩

/-- At the own test the first chain must have sent at least 6 trees and the shared chain at least 2:
the openings are taken 0 0, taken 0 5 and taken 1 1. -/
theorem closed_KWFull : Coin.Closed piKWFull rKWFull codesKeyFull 2 6 2 TKWFull :=
  ⟨piKWFull_planOk, k12Condition_piKWFull_r, by decide +kernel, piKWFull_johOk, piKWFull_bat⟩

/-- Can the test on the place fail? Six plans of trees at which it says no. -/
theorem place_teeth :
    H2K.Member.placeOk piKWFull 2 5 2 TKWFull = false ∧
      H2K.Member.placeOk piKWFull 2 6 1 TKWFull = false ∧
      H2K.Member.placeOk piKWFull 1 6 2 TKWFull = false ∧
      H2K.Member.placeOk piKUFull 1 0 0 TKUFull.dropLast = false ∧
      H2K.Member.placeOk piKOFull 1 0 0 ((.own 1, 21) :: TKOFull.tail.tail) = false ∧
      H2K.Member.placeOk piKUFull 1 0 0 TKOFull = false := by decide +kernel

end H2K.Pub

#print axioms H2K.Pub.codes_held
#print axioms H2K.Pub.closed_KUFull
#print axioms H2K.Pub.closed_KOFull
#print axioms H2K.Pub.closed_KWFull
#print axioms H2K.Pub.place_teeth
#print axioms H2K.Pub.roundsHold_piKUFull
#print axioms H2K.Pub.roundsHold_piKOFull
#print axioms H2K.Pub.roundsHold_piKWFull
#print axioms H2K.Pub.roundsBelowAt_piKWFull
#print axioms H2K.Pub.held_KU
#print axioms H2K.Pub.radii_KU
#print axioms H2K.Pub.trial_KU
#print axioms H2K.Pub.piKUFull_bat
#print axioms H2K.Pub.k12Condition_piKUFull_r
#print axioms H2K.Pub.roundsBelow_piKUFull
#print axioms H2K.Pub.opens_KU
#print axioms H2K.Pub.labelTests_KU
#print axioms H2K.Pub.held_KO
#print axioms H2K.Pub.radii_KO
#print axioms H2K.Pub.trial_KO
#print axioms H2K.Pub.piKOFull_bat
#print axioms H2K.Pub.k12Condition_piKOFull_r
#print axioms H2K.Pub.roundsBelow_piKOFull
#print axioms H2K.Pub.opens_KO
#print axioms H2K.Pub.labelTests_KO
#print axioms H2K.Pub.held_KW
#print axioms H2K.Pub.radii_KW
#print axioms H2K.Pub.trial_KW
#print axioms H2K.Pub.piKWFull_bat
#print axioms H2K.Pub.k12Condition_piKWFull_r
#print axioms H2K.Pub.roundsBelow_piKWFull
#print axioms H2K.Pub.opens_KW
#print axioms H2K.Pub.labelTests_KW
