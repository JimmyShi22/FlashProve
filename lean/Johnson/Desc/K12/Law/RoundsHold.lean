-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RoundsHold.lean: "every written round of a proximity test (the kind K12) is
below", WITH THE RADII PINNED BY FACTS: the form `RoundsHoldAt`; that it gives the library's form
`RoundsBelowAt`; and that both forms read of a place its stages, rows and written rounds alone.

Why a second form. `RoundsBelowAt` (RoundsAtMade.lean) has six clauses: the place's stages; its
written rounds; its chain; the chain's rounds; and two comparisons: "BAT"'s count and the chain's
counts are at most εs of their rounds' verifier messages. It holds no clause on the radii. A bound
on a list is cut off to 0 where the radius is not inside the Johnson bound, so a comparison can pass
at radii at which no law holds: the six can be true there and bear no weight. Whoever spends the six
should take the weight from a fact on the radii beside them: the test `johOk`, or this form.
`RoundsBelowAt` is spent by other files, which open it by its six clauses. So it stays as
it is, and the clauses on the radii stand here under a name of their own.
Main names:
  `RoundsHoldAt p rad εs`: the six clauses, and under the same letters four more: the chain begins
    at the first stage's radius; it has `Chain.Holds`; the facts on codes of the three block laws
    hold at every stage (`CodesAt`); the first stage's words have the Johnson bound's list at its
    radius. No codes of a record stand in it.
  `RoundsHoldAt.below`: it gives `RoundsBelowAt`.
  `batPlaceB`, `batPlaceB_at`: the test on "BAT" at the place itself: the two tests of
    Johnson/Bridge/BatPriced.lean (`good`, `priced`) at the first stage, its radius and the place's
    own rows.
  `roundsHoldAt_of`, `roundsHoldAt_ofB`: from the condition `K12Condition` and these two tests.
  `goodPriced_of_planBats`: the two tests from `planBatsB`.
  `cappedHoldAt_of`: at the cap: each count is at most the round's verifier messages divided by
    2^128, rounded down; the chain's rounds and the clauses on the radii are handed on. It is
    applied at no place here.
  `RoundsBelowAt.congr`, `RoundsHoldAt.congr`: each form at p and radii `rad'` from the form at q
    and `rad`: the same stages, rows and written rounds; the radii agree at the stages. No codes, no
    `pubOk`.
  `roundsHold_at_madeOf_L`, `_U`, `_O`, `_W`: as `roundsBelow_at_madeOf_L` and its like
    (RoundsAtMade.lean), with the stronger conclusion.
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: of the four clauses the first follows from the chain's making (`rad_chainFrom`,
ChainHolds.lean); it is kept for the reader. RoundsNot.lean refutes `RoundsHoldAt` wherever the
first stage's radius is not inside the Johnson bound; that it fails likewise at a later stage's such
radius is by reading `CodesAt`, no theorem. From below nothing pins the radii. One round's share
each, no sum; "BAT"'s number is priced and is no law's count. Nothing on soundness. Nothing on
hiding.

-/
import Johnson.Desc.K12.Law.RoundsAtMade
import Johnson.Desc.K12.Law.CondCongr

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
messages, at radii at which the laws' facts on codes hold.** The first six clauses are
`RoundsBelowAt`'s. The four on the radii: the chain begins at the first stage's radius and has
`Chain.Holds`; the facts on codes of the three block laws hold at every stage (`CodesAt`); the first
stage's words have the Johnson bound's list at its radius. -/
def RoundsHoldAt (p : P12) (rad : Sg → ℕ) (εs : ℝ≥0∞) : Prop :=
  ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
    p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad) rest a l = some c ∧ c.rds = l.map WR.rd ∧
    RoundBelow ((sgOf a).lstJ (rad (sgOf a)) * (p.nums.rows - 1)) w0.rd εs ∧ Err.Below c.err εs ∧
    c.rad = rad (sgOf a) ∧ c.Holds ∧ CodesAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p.nums.stages ∧
    (sgOf a).cIn.ListAt (rad (sgOf a)) ((sgOf a).lstJ (rad (sgOf a)))

/-- **It gives the library's form.** -/
theorem RoundsHoldAt.below {p : P12} {rad : Sg → ℕ} {εs : ℝ≥0∞} (h : RoundsHoldAt p rad εs) :
    RoundsBelowAt p rad εs := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, _⟩ := h
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6⟩

/-- **The test on "BAT" at the place itself**: the two tests of Johnson/Bridge/BatPriced.lean
at the first stage, its radius and the place's own rows: the sizes are in order and the radius is
below the Johnson radius (`good`); the comparison on the count (`priced`). It says no where the
place has no stage. -/
def batPlaceB (p : P12) (rad : Sg → ℕ) : Bool :=
  p.nums.stages.head?.any fun a => (batPlaceOf p rad a).good && (batPlaceOf p rad a).priced

theorem batPlaceB_at {p : P12} {rad : Sg → ℕ} (h : batPlaceB p rad = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest) :
    (batPlaceOf p rad a).good = true ∧ (batPlaceOf p rad a).priced = true := by
  unfold batPlaceB at h
  rw [hs, List.head?_cons, Option.any_some, Bool.and_eq_true] at h
  exact h

/-- From the condition, and the two tests at "BAT"'s place. -/
theorem roundsHoldAt_of {p : P12} {rad : Sg → ℕ} {K : Codes}
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hb : ∀ a rest, p.nums.stages = a :: rest →
      (batPlaceOf p rad a).good = true ∧ (batPlaceOf p rad a).priced = true) :
    RoundsHoldAt p rad ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, _, e6, e7, e8, _⟩ := hK.gives
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4,
    BatPlace.below (hb a rest e1).2 (isRd_bat p.nums w0 l e2), e8, e6, e7, hK.codes,
    BatPlace.listIn (hb a rest e1).1⟩

/-- The same from the one Boolean. -/
theorem roundsHoldAt_ofB {p : P12} {rad : Sg → ℕ} {K : Codes}
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hb : batPlaceB p rad = true) : RoundsHoldAt p rad ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_of hK (batPlaceB_at hb)

/-- From the test `planBatsB`: where "BAT"'s place is among the places that the test zips of
the plans' entries "BAT" and the planner's stages. -/
theorem goodPriced_of_planBats {M : Configured} (hB : planBatsB Rad.planner M = true)
    {x : BatPlace} (hd : x ∈ (planBats Rad.planner M).map (·.2)) :
    x.good = true ∧ x.priced = true := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
  exact (planBatsB_at hB q hq).2

/-- At the cap: each count is at most the round's written verifier messages divided by 2 ^ 128,
rounded down. The chain's rounds and the clauses on the radii are handed on: the two comparisons by
themselves say nothing at a radius at which no law holds. -/
theorem cappedHoldAt_of {p : P12} {rad : Sg → ℕ}
    (h : RoundsHoldAt p rad ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad) rest a l = some c ∧ c.rds = l.map WR.rd ∧
      c.rad = rad (sgOf a) ∧ c.Holds ∧ CodesAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p.nums.stages ∧
      (sgOf a).cIn.ListAt (rad (sgOf a)) ((sgOf a).lstJ (rad (sgOf a))) ∧
      (sgOf a).lstJ (rad (sgOf a)) * (p.nums.rows - 1) * wOf w0.rd ≤
        Fintype.card (wRound w0.rd).Chal / 2 ^ 128 ∧
      Err.le c.err (Err.cap 128 c.sh) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, f1, f2, f3, f4⟩ := h
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, f1, f2, f3, f4, ?_,
    Err.le_cap_of_below_inv 128 c.err e6⟩
  refine Err.entry_le_cap 128 _ _ ?_
  rw [ENNReal.inv_pow]
  exact e5

/-! ## What the two forms read of a place -/

/-- **`RoundsBelowAt` reads of a place its stages, its rows and its written rounds, and the radii at
the stages alone.** -/
theorem RoundsBelowAt.congr {p q : P12} {rad rad' : Sg → ℕ} {εs : ℝ≥0∞}
    (hs : p.nums.stages = q.nums.stages) (h1 : p.nums.rows = q.nums.rows)
    (hW : writtenOf p.nums = writtenOf q.nums)
    (hr : ∀ a ∈ p.nums.stages, rad' (sgOf a) = rad (sgOf a)) (h : RoundsBelowAt q rad εs) :
    RoundsBelowAt p rad' εs := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6⟩ := h
  have hs' : p.nums.stages = a :: rest := hs.trans e1
  have hra : ∀ x ∈ a :: rest, rad (sgOf x) = rad' (sgOf x) := fun x hx =>
    (hr x (by rw [hs']; exact hx)).symm
  have ha : rad (sgOf a) = rad' (sgOf a) := hra a List.mem_cons_self
  refine ⟨a, rest, w0, l, c, hs', hW.trans e2, ?_, e4, ?_, e6⟩
  · rw [← chainFrom_congr Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad rad' rest a l hra]
    exact e3
  · rw [← ha, h1]
    exact e5

/-- **So does the form with the radii pinned.** The chain is the same chain, so what is said of it
is carried over as it stands. -/
theorem RoundsHoldAt.congr {p q : P12} {rad rad' : Sg → ℕ} {εs : ℝ≥0∞}
    (hs : p.nums.stages = q.nums.stages) (h1 : p.nums.rows = q.nums.rows)
    (hW : writtenOf p.nums = writtenOf q.nums)
    (hr : ∀ a ∈ p.nums.stages, rad' (sgOf a) = rad (sgOf a)) (h : RoundsHoldAt q rad εs) :
    RoundsHoldAt p rad' εs := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, f1, f2, f3, f4⟩ := h
  have hs' : p.nums.stages = a :: rest := hs.trans e1
  have hra : ∀ x ∈ a :: rest, rad (sgOf x) = rad' (sgOf x) := fun x hx =>
    (hr x (by rw [hs']; exact hx)).symm
  have ha : rad (sgOf a) = rad' (sgOf a) := hra a List.mem_cons_self
  refine ⟨a, rest, w0, l, c, hs', hW.trans e2, ?_, e4, ?_, e6, f1.trans ha, f2, ?_, ?_⟩
  · rw [← chainFrom_congr Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad rad' rest a l hra]
    exact e3
  · rw [← ha, h1]
    exact e5
  · rw [hs']
    exact codesAt_congr Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad rad' _ hra (by rw [← e1]; exact f3)
  · rw [← ha]
    exact f4

/-! ## At the places made off the three public files -/

section
variable {Cl : Type} {pol lay KL : ByteArray} (m : Made) (hm : madeOf pol lay KL = .ok m)
  (X : Places4) (h : placesOfMade m = .ok X) (place : Place) (K : Codes)
  (hM : planTestsB Rad.planner m.p.chains.made = true)
  (hB : planBatsB Rad.planner m.p.chains.made = true)
include hm h hM hB

theorem roundsHold_at_madeOf_L
    (hw : (baseWorks m.p.chains.made)[0]? =
      some (m.p.chains.made.sized.set.workOf .query .request))
    (hd : ∀ a rest, (proximityTestParametersAt place X.L).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place X.L)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.L) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.L) K = true) :
    RoundsHoldAt (proximityTestParametersAt place X.L)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_of (k12Condition_at_madeOf_L m hm X h place K hM hw hp hpub)
    fun a rest e => goodPriced_of_planBats hB (hd a rest e)

theorem roundsHold_at_madeOf_U
    (hw : (baseWorks m.p.chains.made)[1]? = some (workShared (laterOfProof m 0)))
    (hd : ∀ a rest, (proximityTestParametersAt place X.U).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place X.U)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.U) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.U) K = true) :
    RoundsHoldAt (proximityTestParametersAt place X.U)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_of (k12Condition_at_madeOf_U m hm X h place K hM hw hp hpub)
    fun a rest e => goodPriced_of_planBats hB (hd a rest e)

theorem roundsHold_at_madeOf_O (o : PlaceNums) (ho : X.O = some o)
    (hs : m.p.chains.made.sized.proof.batch.shape.sharedSplitNeeded = true)
    (hw : (baseWorks m.p.chains.made)[2]? = some (workShared (laterOfProof m 0)))
    (hd : ∀ a rest, (proximityTestParametersAt place o).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place o)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place o) K = true) :
    RoundsHoldAt (proximityTestParametersAt place o)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_of (k12Condition_at_madeOf_O m hm X h place K hM o ho hs hw hp hpub)
    fun a rest e => goodPriced_of_planBats hB (hd a rest e)

theorem roundsHold_at_madeOf_W
    (hw : (baseWorks m.p.chains.made)[3]? = some (workOwn (laterOfProof m 0)))
    (hd : ∀ a rest, (proximityTestParametersAt place X.W).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place X.W)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.W) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.W) K = true) :
    RoundsHoldAt (proximityTestParametersAt place X.W)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_of (k12Condition_at_madeOf_W m hm X h place K hM hw hp hpub)
    fun a rest e => goodPriced_of_planBats hB (hd a rest e)

end

end H2K.Pub

#print axioms H2K.Pub.RoundsHoldAt.below
#print axioms H2K.Pub.roundsHoldAt_of
#print axioms H2K.Pub.roundsHoldAt_ofB
#print axioms H2K.Pub.cappedHoldAt_of
#print axioms H2K.Pub.RoundsBelowAt.congr
#print axioms H2K.Pub.RoundsHoldAt.congr
#print axioms H2K.Pub.roundsHold_at_madeOf_L
#print axioms H2K.Pub.roundsHold_at_madeOf_U
#print axioms H2K.Pub.roundsHold_at_madeOf_O
#print axioms H2K.Pub.roundsHold_at_madeOf_W
