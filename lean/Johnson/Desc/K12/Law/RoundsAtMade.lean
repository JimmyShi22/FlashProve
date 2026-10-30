-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K12.Law.CondAtPlanned
import Johnson.Desc.K12.Law.BatOneMade
import Johnson.Bridge.PlanBats
import Iop.ErrCap
/-
Johnson/Desc/K12/Law/RoundsAtMade.lean: every written round of the test, "BAT" included, at the places that are made off the three public files: the general form.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Rad baseWorks planTestsB planBats planBatsB planBatsB_at BatPlace)
open H2U (placesOfMade laterOfProof Places4 PlaceNums proximityTestParametersAt)
open H2K.Made (workShared workOwn places_nums nums_of_planOk written_bat_eq)
open Iop
open scoped ENNReal

/-- **Every written round of a place's test has its count at most εs of its written verifier
messages**, at radii `rad`: the round "BAT" at the Johnson bound's list at the first stage, times
the place's rows less one; the rounds behind it at the counts of the place's chain. -/
def RoundsBelowAt (p : P12) (rad : Sg → ℕ) (εs : ℝ≥0∞) : Prop :=
  ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
    p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad) rest a l = some c ∧ c.rds = l.map WR.rd ∧
    RoundBelow ((sgOf a).lstJ (rad (sgOf a)) * (p.nums.rows - 1)) w0.rd εs ∧ Err.Below c.err εs

/-- The first written round is the format's "BAT" at the place's rows. -/
theorem isRd_bat (N : H2U.TestNums) (w0 : WR) (l : List WR) (hw : writtenOf N = some (w0 :: l)) :
    IsRd w0.rd (Fmt.M2.rBatN N.rows) := by
  refine isRd_of_B ?_
  rw [written_bat_eq N w0 l hw]
  simp [isRdB, H2K.Made.wr, Fmt.M2.rBatN, Fmt.M1.rBat, Fmt.Entry.cut]

/-- The place of "BAT" in the test on the plans' entries "BAT": the first stage, its radius,
the place's rows. -/
def batPlaceOf (p : P12) (rad : Sg → ℕ) (a : Fmt.M1.Stage) : BatPlace :=
  ⟨sgOf a, rad (sgOf a), p.nums.rows⟩

/-- From the condition, and the comparison at "BAT"'s place. -/
theorem roundsBelowAt_of {p : P12} {rad : Sg → ℕ} {K : Codes}
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hb : ∀ a rest, p.nums.stages = a :: rest → (batPlaceOf p rad a).priced = true) :
    RoundsBelowAt p rad ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, _, _, _, e8, _⟩ := hK.gives
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4,
    BatPlace.below (hb a rest e1) (isRd_bat p.nums w0 l e2), e8⟩

/-- From the test `planBatsB`: where "BAT"'s place is among the places that the test zips of
the plans' entries "BAT" and the planner's stages. -/
theorem priced_of_planBats {M : Configured} (hB : planBatsB Rad.planner M = true) {x : BatPlace}
    (hd : x ∈ (planBats Rad.planner M).map (·.2)) : x.priced = true := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
  exact (planBatsB_at hB q hq).2.2

/-- At the cap. -/
theorem cappedAt_of {p : P12} {rad : Sg → ℕ} (h : RoundsBelowAt p rad ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad) rest a l = some c ∧
      (sgOf a).lstJ (rad (sgOf a)) * (p.nums.rows - 1) * wOf w0.rd ≤
        Fintype.card (wRound w0.rd).Chal / 2 ^ 128 ∧
      Err.le c.err (Err.cap 128 c.sh) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, _, e5, e6⟩ := h
  refine ⟨a, rest, w0, l, c, e1, e2, e3, ?_, Err.le_cap_of_below_inv 128 c.err e6⟩
  refine Err.entry_le_cap 128 _ _ ?_
  rw [ENNReal.inv_pow]
  exact e5

section
variable {Cl : Type} {pol lay KL : ByteArray} (m : Made) (hm : madeOf pol lay KL = .ok m)
  (X : Places4) (h : placesOfMade m = .ok X) (place : Place) (K : Codes)
  (hM : planTestsB Rad.planner m.p.chains.made = true)
  (hB : planBatsB Rad.planner m.p.chains.made = true)
include hm h hM hB

theorem roundsBelow_at_madeOf_L
    (hw : (baseWorks m.p.chains.made)[0]? =
      some (m.p.chains.made.sized.set.workOf .query .request))
    (hd : ∀ a rest, (proximityTestParametersAt place X.L).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place X.L)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.L) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.L) K = true) :
    RoundsBelowAt (proximityTestParametersAt place X.L)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelowAt_of (k12Condition_at_madeOf_L m hm X h place K hM hw hp hpub)
    fun a rest e => priced_of_planBats hB (hd a rest e)

theorem roundsBelow_at_madeOf_U
    (hw : (baseWorks m.p.chains.made)[1]? = some (workShared (laterOfProof m 0)))
    (hd : ∀ a rest, (proximityTestParametersAt place X.U).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place X.U)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.U) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.U) K = true) :
    RoundsBelowAt (proximityTestParametersAt place X.U)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelowAt_of (k12Condition_at_madeOf_U m hm X h place K hM hw hp hpub)
    fun a rest e => priced_of_planBats hB (hd a rest e)

theorem roundsBelow_at_madeOf_O (o : PlaceNums) (ho : X.O = some o)
    (hs : m.p.chains.made.sized.proof.batch.shape.sharedSplitNeeded = true)
    (hw : (baseWorks m.p.chains.made)[2]? = some (workShared (laterOfProof m 0)))
    (hd : ∀ a rest, (proximityTestParametersAt place o).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place o)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place o) K = true) :
    RoundsBelowAt (proximityTestParametersAt place o)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelowAt_of (k12Condition_at_madeOf_O m hm X h place K hM o ho hs hw hp hpub)
    fun a rest e => priced_of_planBats hB (hd a rest e)

theorem roundsBelow_at_madeOf_W
    (hw : (baseWorks m.p.chains.made)[3]? = some (workOwn (laterOfProof m 0)))
    (hd : ∀ a rest, (proximityTestParametersAt place X.W).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place X.W)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.W) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.W) K = true) :
    RoundsBelowAt (proximityTestParametersAt place X.W)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelowAt_of (k12Condition_at_madeOf_W m hm X h place K hM hw hp hpub)
    fun a rest e => priced_of_planBats hB (hd a rest e)

end

/-- **The bits of work of the places' numbers, one number a scope**: the setting's for a draw of
positions: at the request's own scope at L and W, at the shared scope at U and O. -/
theorem work_at_madeOf {pol lay KL : ByteArray} (m : Made) (hm : madeOf pol lay KL = .ok m)
    (X : Places4) (h : placesOfMade m = .ok X) :
    X.L.nums.work = m.p.chains.made.sized.set.workOf .query .request ∧
      X.U.nums.work = m.p.chains.made.sized.set.workOf .query .shared ∧
      (∀ o, X.O = some o → o.nums.work = m.p.chains.made.sized.set.workOf .query .shared) ∧
      X.W.nums.work = m.p.chains.made.sized.set.workOf .query .request := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩ :=
    OnBytes.Model.Verify.planned_parts (planned_of_madeOf hm)
  have hot : m.p.chains.made.sized.proof.batch.lines.oneTime = false :=
    (configure_proof_sizes hc).2.2
  obtain ⟨⟨_, wL⟩, g, ⟨_, wU⟩, hO, ⟨_, wW⟩⟩ := places_nums m X h
  refine ⟨wL, ?_, ?_, ?_⟩
  · rw [wU]
    simp [workShared, laterOfProof, hot]
  · intro o ho
    rw [(hO o ho).2]
    simp [workShared, laterOfProof, hot]
  · rw [wW]
    simp [workOwn, laterOfProof, hot]

end H2K.Pub

#print axioms H2K.Pub.isRd_bat
#print axioms H2K.Pub.roundsBelowAt_of
#print axioms H2K.Pub.cappedAt_of
#print axioms H2K.Pub.roundsBelow_at_madeOf_L
#print axioms H2K.Pub.roundsBelow_at_madeOf_U
#print axioms H2K.Pub.roundsBelow_at_madeOf_O
#print axioms H2K.Pub.roundsBelow_at_madeOf_W
#print axioms H2K.Pub.work_at_madeOf
