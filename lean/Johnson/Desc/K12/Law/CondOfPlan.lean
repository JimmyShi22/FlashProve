-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondOfPlan.lean: the condition of the law of a proximity test (the kind K12),
`K12Condition`, from a yes of the test on the planner's records, `planTestsB Rad.planner M`
(Johnson/Bridge/PlanTests.lean), at a place whose stages are those of one of the nine tests.
Statements and proofs.

Main names:
  `brBy rad`: the brackets by computing (Johnson/Bridge/BrOf.lean) at radii that are handed in.
  `testOf_by`: the place's own test at these brackets is `TestAt.of` of its stages with radii.
  `k12Condition_of_planTests`: a yes of `planTestsB Rad.planner M`; the test number i has the
    setting σ, the stages st and the work w; the place's stages, as `sgOf`, are `stageOf` of st; its
    work is w; rad is `radiusOf σ` at each stage of st; the block's test on the plan; `pubOk p K`:
    then `K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K (2⁻¹ ^ 128)`.
It stands over files of Johnson/Bridge/, and so over Cb/Bridge/CodeListRSProved.lean and
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15). It takes no run of their text; it calls their names.
Limits. The premise on rad can be unpayable: rad is a function of a stage's numbers, `radiusOf` of
the planner's group, which holds an integer m beside them: two stages of one test with the same
numbers and different m have no such rad. `Planned.oneDistance` (OnBytes/Params/Planner.lean) asks
that rounds with the same two codes say the same m; that it pays the premise is not shown. No text
that runs asks `planTestsB`; no theorem says that it says yes at a plan. That a place's stages are
the plan's is a premise. Which round "BASE" gives a test its work is by order alone
(PlanTests.lean's own limit). The limits of the condition stand: one round's share of its written
verifier messages, test bits among them: W of the 128 bits are work; no sum over rounds; the round
"BAT" stands in front of the chain and is not in it; of the chain, not of the block. No soundness is
claimed.
Nothing on hiding.

-/
import Johnson.Desc.K12.Law.CondOfTest
import Johnson.Bridge.PlanTests

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Br FoldedPlace SwitchPlace LastPlace TestAt Rad mainOf maskOf stagesBy testBy
  nineTests baseWorks planTestsBy planTestsB)
open Johnson.Top.H (stageOf radiusOf)
open scoped ENNReal

/-- The brackets by computing (Johnson/Bridge/BrOf.lean), at radii that are handed in. -/
def brBy (rad : Sg → ℕ) (s : Sg) : Br × Br := (mainOf s (rad s), maskOf s (rad s))

theorem dropLast_map' {α β : Type} (f : α → β) : ∀ l : List α,
    (l.map f).dropLast = l.dropLast.map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    have ih := dropLast_map' f (b :: l)
    rw [List.map_cons] at ih
    rw [List.map_cons, List.map_cons, List.dropLast_cons₂, List.dropLast_cons₂, List.map_cons, ih]

/-- The place's own test at these brackets is the test of its list of stages with radii. -/
theorem testOf_by (rad : Sg → ℕ) (p : P12) :
    (testOf rad (brBy rad) p).toList =
      ((p.nums.stages.map fun a => (sgOf a, rad (sgOf a))).getLast?.toList.map fun l =>
        TestAt.of (p.nums.stages.map fun a => (sgOf a, rad (sgOf a))).dropLast l p.nums.work) := by
  unfold testOf
  rw [List.getLast?_map, dropLast_map']
  cases p.nums.stages.getLast? with
  | none => rfl
  | some z =>
    simp [TestAt.of, FoldedPlace.of, LastPlace.of, lastAt, brBy, List.map_map, Function.comp_def]
    rfl

/-- **At the planner's record**: the test number i of the nine. -/
theorem k12Condition_of_planTests {Cl : Type} (M : Configured)
    (hM : planTestsB Rad.planner M = true) (i : ℕ) (σ : Setting) (st : List StageSize) (w : ℕ)
    (hi : (nineTests M.sized)[i]? = some (σ, st)) (hw : (baseWorks M)[i]? = some w)
    (p : P12) (K : Codes) (rad : Sg → ℕ)
    (hst : p.nums.stages.map sgOf = st.map fun y => stageOf y.g y.t) (hwork : p.nums.work = w)
    (hrad : ∀ y ∈ st, rad (stageOf y.g y.t) = radiusOf σ y.g)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Cl).planOk = true) (hpub : pubOk p K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hL : (p.nums.stages.map fun a => (sgOf a, rad (sgOf a))) = stagesBy Rad.planner σ st := by
    have h1 := congrArg (List.map fun s : Sg => (s, rad s)) hst
    rw [List.map_map, List.map_map] at h1
    unfold stagesBy
    refine h1.trans (List.map_congr_left fun y hy => ?_)
    show (stageOf y.g y.t, rad (stageOf y.g y.t)) = (stageOf y.g y.t, radiusOf σ y.g)
    rw [hrad y hy]
  have hmem : ∀ T ∈ testBy Rad.planner σ st w, T ∈ planTestsBy Rad.planner M := by
    intro T hT
    unfold planTestsBy
    rw [List.mem_flatten]
    refine ⟨testBy Rad.planner σ st w, ?_, hT⟩
    refine List.mem_of_getElem? (i := i) ?_
    rw [List.getElem?_zipWith, hi, hw]
  have hall : ∀ T ∈ planTestsBy Rad.planner M, T.ok = true := by
    unfold planTestsB at hM
    simp only [Bool.and_eq_true] at hM
    exact List.all_eq_true.1 hM.1.2
  have hlist := testOf_by rad p
  rw [hL, hwork] at hlist
  cases hT : testOf rad (brBy rad) p with
  | none =>
    exfalso
    obtain ⟨a, rest, _, _, _, _, _, hs, _⟩ := made_of_planOk p hp
    unfold testOf at hT
    rw [hs] at hT
    cases hz : (a :: rest).getLast? with
    | none => simp at hz
    | some z => rw [hz] at hT; cases hT
  | some T =>
    rw [hT] at hlist
    have hTm : T ∈ testBy Rad.planner σ st w := by
      unfold testBy
      rw [← hlist]
      simp
    exact k12Condition_of_test rad (brBy rad) p K T hT (hall T (hmem T hTm)) hp hpub

end H2K.Pub

#print axioms H2K.Pub.k12Condition_of_planTests
