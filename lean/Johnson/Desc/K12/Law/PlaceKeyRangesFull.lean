-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean: the fourth place of a proximity test (the kind K12)
in the key file at the full size: the ranges' test, on the first chain, at ⟨1, none, 5, .K12⟩: as
closed terms; and closed facts on it, each by an evaluation in Lean's kernel. It stands beside
Johnson/Desc/K12/Law/PlacesKeyFull.lean, whose head says of this place: "is not here";
StretchKeyFull.lean; RoundsAtKeyPlaces.lean.

Main names: all in the namespace `H2K.Member`.
  `nKRFull`   the place's numbers, in the type that `Key.rangesNumbers` returns
      (Johnson/Desc/Key/Ranges.lean).
  `piKRFull`   the place. `params_KR`: it is `Key.rangesParams nKRFull`.
  `held_KR`   seven fields of the closed place (stages, rows, work, own mask, the codes' numbers,
      answers, early) are what the library's typed sizes of a key (`Lk6.AtPlan.keyFull`,
      Johnson/Goal/PlanValues/KeySizedReturns.lean) and the typed setting (`setAt`) give by the
      text of `Key.rangesNumbers`. For these no print is trusted.
  `piKRFull_planOk`, `_pubOk`, `_asksOnPlan`   the block's own test on the plan; its public test at
      the key file's table of codes (`codesKeyFull`); what the seat asks on the plan.
  `rounds_KRFull`, `bat_KRFull`, `stretch_KRFull`, `roots_KRFull`   the closed place has declared
      rounds; the first chain's first round named "BAT" is number 18805 of the written list
      (`dryKeyFull`, Johnson/G/DryKeyLit.lean); from there on the written rounds are the place's,
      written out; two roots are sent in front. `stretch_KRFull_no`: a control: one round later the
      stretch is another.

Limits. The numbers were typed by a program off the print of a run of Lean's evaluator:
`Johnson.G.OfPlan.madeOf` at the library's own full-size texts of the three public files
(Johnson/G/KitFull.lean), then the key file's description's own maker `Key.rangesNumbers` [the
print is not in this library; its sha256 is
5bf404a42dab3d76ab0bd5f9bb17493403a13d81ca4e3aeac1e19a00fd9a494d]. Three numbers are a print's word
still: the first switch's declared opening (`first`), the first free own number (`free`) and where
the stretch begins (`start`); they are held here against the written list, which is what another
print of the planner showed: a check of copying, no second witness. The chain (1), the first tree
(0) and the number of the first group (1) are written numbers in the text of `Key.rangesNumbers`.
That a description makes this place at any public files is not said here. No radii, no price of a
round: nothing of RoundsAtKeyPlaces.lean's condition is here. No soundness is claimed. Nothing on
hiding.
-/
import Johnson.Desc.K12.Law.StretchKeyFull
import Johnson.Desc.K12.Law.Sizes.StagesFull
import Johnson.Desc.Key.Ranges
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Member
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Johnson.G (dryKeyFull)
open H2U (roundsOfNums batPlaces)

/-- The numbers of the ranges' test's place in the key file, at the full size. -/
def nKRFull : H2U.PlaceNums :=
  { chain := 1,
    start := 18805,
    nums :=
      { rows := 981,
        work := 32,
        stages :=
          [⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 4, 49⟩,
           ⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 4, 3, 39⟩,
           ⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 3, 33⟩,
           ⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩],
        ownMask := false,
        «first» := [({ a := 22, W := 77, stored := false, tree := 1 }, Fmt.TreeSource.own 1)],
        free := 2,
        firstTree := 0 },
    idx := [(12, 11), (13, 12), (14, 13), (15, 14)],
    firstGroup := 1,
    answers := 1,
    early := true }

/-- The key file's place of the ranges' test, at the full size. -/
def piKRFull : P12 :=
  { place :=
      { chain := 1, link := none, piece := 5, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 981,
        work := 32,
        stages :=
          [⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 4, 49⟩,
           ⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 4, 3, 39⟩,
           ⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 3, 33⟩,
           ⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩],
        ownMask := false,
        «first» := [({ a := 22, W := 77, stored := false, tree := 1 }, Fmt.TreeSource.own 1)],
        free := 2,
        firstTree := 0 },
    idx := [(12, 11), (13, 12), (14, 13), (15, 14)],
    oracles :=
      [[], [], [], [], [], [],
       [{ logLength := 19,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [1] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 17,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [2] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 20,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [3] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(1, 1)],
    answers := 1,
    early := true }

/-- The closed place is the description's own function of the closed numbers. -/
theorem params_KR : VerifiableInference.Desc.Key.rangesParams nKRFull = piKRFull := rfl

/-- Seven fields of the closed place are what the typed sizes of a key and the typed setting give by
the text of `Key.rangesNumbers`: by the kernel. No print is trusted for these. -/
theorem held_KR :
    piKRFull.nums.stages = Lk6.AtPlan.keyFull.ranges.test.stages.map H2U.stageNums ∧
      piKRFull.nums.rows =
        OnBytes.Wf.rowsBatched Lk6.AtPlan.keyFull.ranges.x Lk6.AtPlan.keyFull.ranges.matrix ∧
      piKRFull.nums.work = setAt.workOf .query .once ∧
      piKRFull.nums.ownMask = !Lk6.AtPlan.keyFull.ranges.x.choice.masksRide ∧
      piKRFull.idx = Lk6.AtPlan.keyFull.ranges.x.stages.map (fun s => (s.code, s.maskCode)) ∧
      piKRFull.answers = setAt.samples ∧
      piKRFull.early = Lk6.AtPlan.keyFull.ranges.x.choice.masksRide := by decide +kernel

theorem piKRFull_planOk : (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).planOk = true := by
  decide +kernel

theorem piKRFull_pubOk : H2K.Pub.pubOk piKRFull codesKeyFull = true := by decide +kernel

theorem piKRFull_asksOnPlan : VerifiableInference.Desc.Key.asksOnPlan piKRFull = true := by
  decide +kernel

/-- The written rounds of a key file's first chain. -/
def xsKFirst : List Fmt.Round := dryKeyFull.1.map (·.1)

theorem rounds_KRFull : roundsOfNums piKRFull.nums = some (dsOf piKRFull) := by decide +kernel

theorem bat_KRFull : (batPlaces (xsKFirst.map (·.entry)))[0]? = some 18805 := by decide +kernel

theorem stretch_KRFull : (dsOf piKRFull).mapM (·.round []) =
    some ((xsKFirst.drop 18805).take (dsOf piKRFull).length) := by decide +kernel

theorem roots_KRFull : ((xsKFirst.take 18805).map (·.entry.roots)).sum = 2 := by decide +kernel

theorem stretch_KRFull_no : ((dsOf piKRFull).mapM (·.round []) ==
    some ((xsKFirst.drop 18806).take (dsOf piKRFull).length)) = false := by decide +kernel

end H2K.Member

#print axioms H2K.Member.params_KR
#print axioms H2K.Member.held_KR
#print axioms H2K.Member.piKRFull_planOk
#print axioms H2K.Member.piKRFull_pubOk
#print axioms H2K.Member.piKRFull_asksOnPlan
#print axioms H2K.Member.rounds_KRFull
#print axioms H2K.Member.bat_KRFull
#print axioms H2K.Member.stretch_KRFull
#print axioms H2K.Member.roots_KRFull
#print axioms H2K.Member.stretch_KRFull_no
#print axioms H2K.Member.nKRFull
#print axioms H2K.Member.piKRFull
#print axioms H2K.Member.xsKFirst
