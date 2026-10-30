-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`E2E/RadiiAreThePlans.lean`: the stages and the decoding radii of the nine proximity tests that are written out in the library (four
of the proof file, four of the key file, one of the copy's file) are those that the verifier's planner derives from public files in
scope.

The library's statement on a proximity test (`H2K.Pub.K12Condition`, `k12Condition_of_test`, `k12Condition_at_written`) takes its
radii as a parameter `rad`. Where it is proved at the full size, `rad` is read by `H2K.Pub.radOf` off a list of nine tests that is
written out in the library, `Johnson.Bridge.testsFull`. This file shows that the stages and the radii of that list are those of a
plan computed from the files.

What this file proves.
* `nine_in_scope`: under the premise `H2K.Sizes.LayoutGroupsAre`, for all `Z` in scope and every plan `p` that the verifier's
  planner returns at `Z`, `nineTests p.chains.made.sized = typedNine`. Here `typedNine` is the nine lists of sized stages with their
  settings, as terms of the library without free variables, in the planner's order: the proof file's last test behind the links,
  folded row, Omega, own test; the key file's ranges, folded row, Omega, own test; the copy's file's test.
* `written_is_derived` (by Lean's kernel): at each of the nine, the planner's stages, each with the planner's radius, are the
  written test's stages with radii. The planner's radius is `Rad.planner = Johnson.Top.H.radiusOf`: the upper end of the group's
  derived relative radius times the main code's length, rounded down. `order` = [5, 6, 7, 8, 0, 1, 2, 3, 4] gives the written list's
  numbers in the planner's order.
* `looked_up_is_derived` (by Lean's kernel): at each stage of each of the nine, the radius that `radOf` looks up in the written test
  is the planner's.
* `radii_are_the_plans`: under the same premise, in scope, at every plan, for each of the nine: the planner's test and the written
  test of the matching number have the same stages with the same radii, and `radOf` of the written test at each of the plan's stages
  is `radiusOf` at the plan's own setting and group.
* `whole_nine_of_the_test`, `under_the_head`: in scope, where the verifier's public part (`ProofFile.pureRoad.pub`) returns and its own
  test on the computed plan, `madePinnedAt`, returns true, the nine tests built from the plan at the planner's radii are the nine
  written tests entire, as values of `Johnson.Bridge.TestAt`: stages, radii, proof-of-work bits and the numbers that the library
  calls brackets. These are calls of the library's `tests_of_free` (`Johnson/Bridge/TestsAtMade.lean`) and `made_in_scope`
  (`Johnson/Goal/Numbers/MadeInScope.lean`). `under_the_head` states this and the two facts of `radii_are_the_plans` under
  `P5J.AtMg` (the library's bundle of premises: the files are in scope and read, the verifier's description is built from them, and
  its tests on the plan return true), and adds that the record of the proof file's last test behind the links, built from the plan,
  is the written one (`H2U.p12OfMade Zp.made = piLFull`).
* `comparison_can_fail`: the comparison `sameStagesAndRadii` is not vacuous: against the neighbouring written test it returns false
  at all nine. `lengths`, `nine_written`: nine of each; the written sizes' nine tests are `typedNine`.

What this file does not say.
* From the scope alone only stages and radii are tied. A written test also holds brackets and proof-of-work bits: these are tied
  only where `madePinnedAt` returns true (`whole_nine_of_the_test`). Which proof-of-work bits belong to which test is by order alone
  (a limit stated in `Johnson/Bridge/PlanTests.lean`).
* The statements go one way: from a planner that returns. That `Model.Verify.planned` returns at files in scope is not shown here.
* That the protocol object `protocolAtFiles Z`, or the description that `verify` runs, takes the stages of its tests from that plan is not shown
  here (the library's `PlacesAtScope.lean` and `RoundsAtKeyPlaces.lean` speak of the tests' places).
* Which radii each caller beneath the soundness theorem passes to the statement on proximity tests is not proved here.
* The groups of the proof file's links, the batching in front of a test and the messages of sendings are in none of the nine (for
  the sendings see `Johnson/G/PackLitArms.lean`, at a literal list).
* The statements from the scope carry one premise without free variables, `H2K.Sizes.LayoutGroupsAre` (the reader of the stored
  layout file returns the library's group lines), needed for the proof file's last test alone. It is a theorem of the side library
  (`AtFullSide/LayoutRead/GroupsPaid.lean`); `AtFullSide/E2E/RadiiAreThePlansInScope.lean` supplies it. `under_the_head` does not
  need it.
* This file depends on files of `Johnson/Bridge/`, and so on `Cb/Bridge/` and on the files under `ThirdParty/`, which are
  adapted from ArkLib and Mathlib (`lean/LIMITS.md`, L15). It copies no passage of their text.
* Facts evaluated by `decide +kernel` are used here and beneath.
-/
import Johnson.Desc.K12.Law.Sizes.PlacesAtScope
import Johnson.Desc.K12.Law.CondMembers
import Johnson.Goal.PlanValues.KeyFullAtScope
import Johnson.Goal.Conditions.LinkTypedAtLines
import Johnson.Bridge.TestsAtMade
import Johnson.AtFull.Shape.TestNumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Bridge.AtPlan
open OnBytes OnBytes.Params
open Johnson.Bridge (TestAt testsFull nineTests stagesBy Rad planTestsBy)
open Johnson.Top.H (stageOf radiusOf)
open H2K.Pub (radOf testNo)
open H2K.Member Lk6.AtPlan H2K.Sizes

/-- **The nine lists of sized stages with their settings**, terms of the library without free variables, in the planner's order. -/
def typedNine : List (Setting × List StageSize) :=
  [(setAt, szLFull), (setAt, szUFull), (setAt, szOFull), (setAt, szWFull),
   (keyFull.set, keyFull.ranges.test.stages), (keyFull.set, keyFull.once.folded.stages),
   (keyFull.set, keyFull.once.omega.stages), (keyFull.set, keyFull.once.own.stages),
   (settingOf recordLines, recordStages)]

/-- **In scope the planner's nine tests are `typedNine`.** -/
theorem nine_in_scope (groups : LayoutGroupsAre) {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
    (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    nineTests p.chains.made.sized = typedNine := by
  have A := atFull_at_scope scope hp
  have hL := last_at_scope groups scope hp
  have hK := key_eq_at_scope scope hp
  obtain ⟨l, rest, shapes, hl, hm⟩ := Model.Verify.planned_madeKey hp
  obtain ⟨hs, T, hT, hLk⟩ := sized_link (configure_sized hm)
  obtain ⟨b', hb⟩ := Johnson.G.ScopeLines.inScope_reads scope
  have e : l = recordLines := by
    rw [hb] at hl
    injection hl with hl
    injection hl with h1 _
    exact h1.symm
  subst e
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  have hq := Option.some.inj (hLk.symm.trans record_link)
  have q1 : p.chains.made.sized.link = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ :=
    congrArg Prod.fst hq
  unfold nineTests Johnson.Bridge.proofTests Johnson.Bridge.keyTests typedNine
  rw [A.setP, hL, A.U, A.O, A.W, hK, hs, q1]
  rfl

/-- The written list's numbers, in the planner's order. -/
def order : List ℕ := [5, 6, 7, 8, 0, 1, 2, 3, 4]

/-- The comparison of one planner's test with one written test: the same stages with the same radii. -/
def sameStagesAndRadii (x : Setting × List StageSize) (T : TestAt) : Bool :=
  decide (stagesBy Rad.planner x.1 x.2 = T.stages)

/-- **The written tests' stages and radii are the derived ones**, at each of the nine. By Lean's kernel. -/
theorem written_is_derived :
    ((typedNine.zip order).all fun x => sameStagesAndRadii x.1 (testNo testsFull x.2)) = true := by
  decide +kernel

/-- **The radius that is looked up in the written test is the planner's**, at each stage of each of the nine. By Lean's kernel. -/
theorem looked_up_is_derived :
    ((typedNine.zip order).all fun x => x.1.2.all fun y =>
      radOf (testNo testsFull x.2) (stageOf y.g y.t) == radiusOf x.1.1 y.g) = true := by
  decide +kernel

/-- A control: against the next written test each comparison returns false. -/
theorem comparison_can_fail :
    ((typedNine.zip order).any fun x => sameStagesAndRadii x.1 (testNo testsFull ((x.2 + 1) % 9))) = false := by
  decide +kernel

/-- Nine and nine. -/
theorem lengths : typedNine.length = 9 ∧ order.length = 9 ∧ testsFull.length = 9 := ⟨rfl, rfl, rfl⟩

/-- **In scope, at every plan: the planner's nine tests and the nine written tests have the same stages with the same radii.** -/
theorem radii_are_the_plans (groups : LayoutGroupsAre) {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
    (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∀ x ∈ (nineTests p.chains.made.sized).zip order,
      stagesBy Rad.planner x.1.1 x.1.2 = (testNo testsFull x.2).stages ∧
      ∀ y ∈ x.1.2, radOf (testNo testsFull x.2) (stageOf y.g y.t) = radiusOf x.1.1 y.g := by
  rw [nine_in_scope groups scope hp]
  intro x hx
  refine ⟨of_decide_eq_true (List.all_eq_true.1 written_is_derived x hx), fun y hy => ?_⟩
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 looked_up_is_derived x hx) y hy)

/-! ## Under the verifier's own test on the plan: the nine tests entire -/

open VerifiableInference.PlanWritten (madePinnedAt pinnedAt_of_row)
open VerifiableInference.PlanWritten.Joined (made_in_scope writtenSized)
open Johnson.G.MadeFree (Free)

/-- **In scope, where the verifier's public part is returned and its test on the computed plan returns true: the nine tests that are built from that plan, at
the planner's radii, are the nine written tests entire**: stages, radii, proof-of-work bits, brackets. Two calls of the library's statements (tests_of_free,
made_in_scope). -/
theorem whole_nine_of_the_test {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} (scope : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    planTestsBy Rad.planner Z.p.chains.made = testsFull.drop 5 ++ testsFull.take 5 :=
  Johnson.Bridge.AtMade.tests_of_free (made_in_scope scope h hy)

/-- The written sizes' nine tests are `typedNine`. By Lean's kernel. -/
theorem nine_written : nineTests writtenSized = typedNine := by decide +kernel

section Head
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under `P5J.AtMg`** (the files are in scope and read, the verifier's description is built from them, and its tests on the plan return true): (1) the nine
tests built from the public part's own plan at the planner's radii are the nine written tests entire; (2) at each of the nine the radius that radOf looks up in
the written test is radiusOf at the plan's own setting and group; (3) the record of the proof file's last test behind the links that is built from the plan is the
written record `piLFull` (from the library's p12_four_at_head), at which the statement on proximity tests is proved with these radii. -/
theorem under_the_head (h : P5J.AtMg o Z D r Zp Np cF) :
    planTestsBy Rad.planner Zp.p.chains.made = testsFull.drop 5 ++ testsFull.take 5 ∧
    (∀ x ∈ (nineTests Zp.p.chains.made.sized).zip order,
      stagesBy Rad.planner x.1.1 x.1.2 = (testNo testsFull x.2).stages ∧
      ∀ y ∈ x.1.2, radOf (testNo testsFull x.2) (stageOf y.g y.t) = radiusOf x.1.1 y.g) ∧
    H2U.p12OfMade Zp.made = piLFull := by
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨hm, -⟩ := h.pins
  have hy := pinnedAt_of_row (Z := Zp) (by rw [hm, Bool.or_true])
  have hsz : Zp.p.chains.made.sized = writtenSized :=
    congrArg Free.sized (made_in_scope h.scope hZ hy)
  refine ⟨whole_nine_of_the_test h.scope hZ hy, ?_, Johnson.AtFull.Shape.p12_at_head h⟩
  rw [hsz, nine_written]
  intro x hx
  refine ⟨of_decide_eq_true (List.all_eq_true.1 written_is_derived x hx), fun y hy => ?_⟩
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 looked_up_is_derived x hx) y hy)

end Head

end Johnson.Bridge.AtPlan

#print axioms Johnson.Bridge.AtPlan.whole_nine_of_the_test
#print axioms Johnson.Bridge.AtPlan.nine_written
#print axioms Johnson.Bridge.AtPlan.under_the_head
#check @Johnson.Bridge.AtPlan.under_the_head
#print axioms Johnson.Bridge.AtPlan.nine_in_scope
#print axioms Johnson.Bridge.AtPlan.written_is_derived
#print axioms Johnson.Bridge.AtPlan.looked_up_is_derived
#print axioms Johnson.Bridge.AtPlan.comparison_can_fail
#print axioms Johnson.Bridge.AtPlan.lengths
#print axioms Johnson.Bridge.AtPlan.radii_are_the_plans
#check @Johnson.Bridge.AtPlan.radii_are_the_plans
#check @Johnson.Bridge.AtPlan.nine_in_scope
