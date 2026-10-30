-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondAtMade.lean: the condition of the law of a proximity test (the kind K12),
`K12Condition`, at the four places that `H2U.placesOfMade` makes off the made plan, from tests on
the planner's record alone, the block's test on the plan and `pubOk`. Definitions, statements and
proofs.

Why. `k12Condition_of_planTests` (Johnson/Desc/K12/Law/CondOfPlan.lean) has five premises that tie a
place to one of the planner's nine tests. At a place that is made off the plan four of them are paid
here by unfolding the makers' texts.
Main names:
  `stages_tie`: `sgOf (stageNums y)` is `stageOf y.g y.t`.
  `radBy σ st`: the planner's radius (`radiusOf`) at a stage of a list, looked up by the stage's
    nine numbers. `oneRadB σ st`: two stages of the list with the same nine numbers have one radius:
    a test. `radBy_at`: under it `radBy` is `radiusOf` at every stage of the list.
  `k12Condition_at_made`: at the test number i of the nine.
  `k12Condition_at_made_L`, `_U`, `_O`, `_W`: with M := `m.p.chains.made`: `placesOfMade m = .ok X`;
    `planTestsB Rad.planner M = true`; the round "BASE" number 0, 1, 2 or 3 of the plans has the
    setting's bits of work at the test's scope; `oneRadB` at the test's stages; the block's test on
    the plan and `pubOk` at `proximityTestParametersAt place X.L` …: then `K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ` at
    `radBy` of these stages, that place and 2⁻¹ ^ 128.
It stands over files of Johnson/Bridge/, and so over Cb/Bridge/CodeListRSProved.lean and
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15). It takes no run of their text; it calls their names.
Limits: no member is shown: m is a variable. No text that runs asks `planTestsB`, the premise on the
round "BASE", or `oneRadB`; all three read the planner's record alone. The work is read at
`M.sized.set`, the radii at `M.sized.proof.set`: that the two are one setting is neither used nor
shown. The limits of the condition stand: one round's share of its written verifier messages, test
bits among them: W of the 128 bits are work; no sum over rounds; the round "BAT" stands in front of
the chain and is not in it; of the chain, not of the block. No soundness is claimed. Nothing on
hiding.

-/
import Johnson.Desc.K12.Law.CondOfPlan
import Johnson.Desc.K12.Law.CondAtWritten
import Johnson.Desc.K12.Law.PlacesNums

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Rad nineTests baseWorks planTestsB)
open Johnson.Top.H (stageOf radiusOf)
open H2U (placesOfMade laterOfProof stageNums Places4 PlaceNums proximityTestParametersAt)
open H2K.Made (places_nums nums_of_planOk workShared workOwn)
open scoped ENNReal

/-- A stage of a place that is made off the plan, read as the proof library's stage, is the
planner's group read so. -/
theorem stages_tie (st : List StageSize) :
    (st.map stageNums).map sgOf = st.map fun y => stageOf y.g y.t := by
  rw [List.map_map]
  exact List.map_congr_left fun _ _ => rfl

theorem sgEq_self (s : Sg) : sgEq s s = true := by simp [sgEq]

/-- The planner's radius at a stage of a list, looked up by the stage's nine numbers. -/
def radBy (σ : Setting) (st : List StageSize) (s : Sg) : ℕ :=
  ((st.find? fun y => sgEq (stageOf y.g y.t) s).map fun y => radiusOf σ y.g).getD 0

/-- Two stages of the list with the same nine numbers have one radius: a test. -/
def oneRadB (σ : Setting) (st : List StageSize) : Bool :=
  st.all fun y => st.all fun y' =>
    !sgEq (stageOf y.g y.t) (stageOf y'.g y'.t) || radiusOf σ y.g == radiusOf σ y'.g

theorem radBy_at {σ : Setting} {st : List StageSize} (h : oneRadB σ st = true) :
    ∀ y ∈ st, radBy σ st (stageOf y.g y.t) = radiusOf σ y.g := by
  intro y hy
  unfold radBy
  cases hf : st.find? fun y' => sgEq (stageOf y'.g y'.t) (stageOf y.g y.t) with
  | none =>
    have := List.find?_eq_none.1 hf y hy
    rw [sgEq_self] at this
    exact absurd rfl this
  | some y0 =>
    have h0 : y0 ∈ st := List.mem_of_find?_eq_some hf
    have hp : sgEq (stageOf y0.g y0.t) (stageOf y.g y.t) = true :=
      List.find?_some (p := fun y' : StageSize => sgEq (stageOf y'.g y'.t) (stageOf y.g y.t)) hf
    unfold oneRadB at h
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h y0 h0) y hy
    rw [hp] at h2
    simpa using h2

/-- **The tie**, at the test number i of the nine. -/
theorem k12Condition_at_made {Cl : Type} (M : Configured) (i : ℕ) (st : List StageSize)
    (hi : (nineTests M.sized)[i]? = some (M.sized.proof.set, st)) (x : PlaceNums)
    (hx : x.nums.stages = st.map stageNums) (place : Place) (K : Codes)
    (hM : planTestsB Rad.planner M = true) (hw : (baseWorks M)[i]? = some x.nums.work)
    (h1 : oneRadB M.sized.proof.set st = true)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place x) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place x) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radBy M.sized.proof.set st) (proximityTestParametersAt place x) K
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_of_planTests M hM i _ st x.nums.work hi hw (proximityTestParametersAt place x) K _
    (by rw [nums_of_planOk place x hp, hx]; exact stages_tie st)
    (by rw [nums_of_planOk place x hp]) (radBy_at h1) hp hpub

section
variable {Cl : Type} (m : Made) (X : Places4) (h : placesOfMade m = .ok X) (place : Place)
  (K : Codes) (hM : planTestsB Rad.planner m.p.chains.made = true)
include h hM

/-- The first chain's last test. -/
theorem k12Condition_at_made_L
    (hw : (baseWorks m.p.chains.made)[0]? =
      some (m.p.chains.made.sized.set.workOf .query .request))
    (h1 : oneRadB m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages = true)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.L) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.L) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages)
      (proximityTestParametersAt place X.L) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_made _ 0 _ rfl X.L (places_nums m X h).1.1 place K hM
    (by rw [(places_nums m X h).1.2]; exact hw) h1 hp hpub

/-- The folded row's test. -/
theorem k12Condition_at_made_U
    (hw : (baseWorks m.p.chains.made)[1]? = some (workShared (laterOfProof m 0)))
    (h1 : oneRadB m.p.chains.made.sized.proof.set
      m.p.chains.made.sized.proof.batch.folded.stages = true)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.U) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.U) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages)
      (proximityTestParametersAt place X.U) K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨_, g, hU, _, _⟩ := places_nums m X h
  exact k12Condition_at_made _ 1 _ rfl X.U hU.1 place K hM (by rw [hU.2]; exact hw) h1 hp hpub

/-- Omega's test. -/
theorem k12Condition_at_made_O (o : PlaceNums) (ho : X.O = some o)
    (hw : (baseWorks m.p.chains.made)[2]? = some (workShared (laterOfProof m 0)))
    (h1 : oneRadB m.p.chains.made.sized.proof.set
      m.p.chains.made.sized.proof.batch.omega.stages = true)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place o) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      (proximityTestParametersAt place o) K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨_, g, _, hO, _⟩ := places_nums m X h
  exact k12Condition_at_made _ 2 _ rfl o (hO o ho).1 place K hM (by rw [(hO o ho).2]; exact hw) h1
    hp hpub

/-- The own test. -/
theorem k12Condition_at_made_W
    (hw : (baseWorks m.p.chains.made)[3]? = some (workOwn (laterOfProof m 0)))
    (h1 : oneRadB m.p.chains.made.sized.proof.set
      m.p.chains.made.sized.proof.batch.own.stages = true)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.W) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.W) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages)
      (proximityTestParametersAt place X.W) K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨_, g, _, _, hW⟩ := places_nums m X h
  exact k12Condition_at_made _ 3 _ rfl X.W hW.1 place K hM (by rw [hW.2]; exact hw) h1 hp hpub

end

end H2K.Pub

#print axioms H2K.Pub.k12Condition_at_made
#print axioms H2K.Pub.k12Condition_at_made_L
#print axioms H2K.Pub.k12Condition_at_made_U
#print axioms H2K.Pub.k12Condition_at_made_O
#print axioms H2K.Pub.k12Condition_at_made_W
