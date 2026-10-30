-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/FileWeights.lean: THE NAMED TEST "weights" ON A KEY FILE's SOURCE
(`weightsCovered`, Johnson/Desc/Key/Source.lean) AT THE FULL SIZE: the lookup on the numbers of two
digits reaches every unit of two digits of the committed matrix's layout, and nothing outside them.

What the test reads: the units of rows of the layout, and the ranges as read back from the key
file's parameter bytes. At the full size the layout is what `Model.wsLayOf` makes of ten written
sizes (`wsFull`, Johnson/Top/H/LooksAtPlan.lean) and the written lines' number of column bits; the
ranges are `keyFull`'s (Johnson/Goal/PlanValues/KeySizedReturns.lean).

  `weightsB`: the closed question: the layout is made, and the test accepts at its units and the
    written ranges.
  **`weightsB_full`**: it holds. By Lean's kernel (`decide +kernel`), behind one rewriting: the test
    sorts short lists by `List.mergeSort`, which the kernel does not evaluate; `mergeSort_eq`
    (Johnson/Unfolds/MergeSort.lean) puts a text in its place that it does.
  `weightsB_rejects`, `weightsB_rejects_outside`: two negative tests: with the first part of every
    lookup left out, and with one run more in every part, far beyond the matrix's rows, the test
    rejects.
  `weightsHalves`, `halves_full`: which half rejects: the test's two halves ("every run lies inside
    a unit"; "every unit is reached whole") asked each alone: at the written ranges both accept;
    with a part left out the second alone rejects; with a run outside the first alone.
  `weights_full`: so, at whatever layout that call returns, the test accepts.
  **`weights_ok`**: where `sourceOf m` returns X, m's layout is that call's value and the ranges as
    read are the written ones: the clause's own expression, "= true".

Limits. The full size alone. The three premises of `weights_ok` are not shown here. Nothing on what
the test is worth. Nothing on soundness.
-/
import Johnson.Desc.Key.Desc
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Unfolds.MergeSort
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open Johnson.G.OfPlan (Made)
open Lk6.AtPlan (keyFull wsFull)
open VerifiableInference.Desc.Key (weightsCovered unitsReached runsInUnits twoDigitUnits sourceOf
  Source)

/-- The closed question, at ranges x: the layout is made, and the test accepts at its units. -/
def weightsB (x : WfPublic) : Bool :=
  match Model.wsLayOf wsFull true recordLines.blockLog with
  | .ok Y => weightsCovered (Plan.unitsOfLayout Y) x
  | .error _ => false

set_option maxRecDepth 1000000 in
/-- **It holds at the written ranges.** -/
theorem weightsB_full : weightsB keyFull.ranges.x = true := by
  unfold weightsB weightsCovered unitsReached
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with the first part of every lookup left out. -/
theorem weightsB_rejects : weightsB { keyFull.ranges.x with
    lookups := keyFull.ranges.x.lookups.map fun l => { l with parts := l.parts.drop 1 } } =
    false := by
  unfold weightsB weightsCovered unitsReached
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A second negative test: with one run more in every part, far beyond the matrix's rows. Which
half rejects is `halves_full`'s to say. -/
theorem weightsB_rejects_outside : weightsB { keyFull.ranges.x with
    lookups := keyFull.ranges.x.lookups.map fun l =>
      { l with parts := l.parts.map fun p => { p with runs := p.runs ++ [⟨0, 10 ^ 9, 1, 1⟩] } } } =
    false := by
  unfold weightsB weightsCovered unitsReached
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

/-! ## Which half rejects -/

/-- The ranges with the first part of every lookup left out. -/
def xMissing : WfPublic := { keyFull.ranges.x with
  lookups := keyFull.ranges.x.lookups.map fun l => { l with parts := l.parts.drop 1 } }

/-- The ranges with one run more in every part, far beyond the matrix's rows. -/
def xOutside : WfPublic := { keyFull.ranges.x with
  lookups := keyFull.ranges.x.lookups.map fun l =>
    { l with parts := l.parts.map fun p => { p with runs := p.runs ++ [⟨0, 10 ^ 9, 1, 1⟩] } } }

/-- The test's two halves, each alone, at each lookup with the table of the numbers of two digits:
"every run lies inside a unit"; "every unit is reached whole". -/
def weightsHalves (x : WfPublic) : List (Bool × Bool) :=
  match Model.wsLayOf wsFull true recordLines.blockLog with
  | .ok Y => (x.lookups.filter fun l => l.d == Plan.weightBits).map fun l =>
      (runsInUnits (twoDigitUnits (Plan.unitsOfLayout Y)) l,
        unitsReached (twoDigitUnits (Plan.unitsOfLayout Y)) l)
  | .error _ => []

set_option maxRecDepth 1000000 in
/-- One such lookup; both halves accept; with a part left out the second alone rejects; with a run
outside the first alone. -/
theorem halves_full : (weightsHalves keyFull.ranges.x, weightsHalves xMissing,
    weightsHalves xOutside) = ([(true, true)], [(true, false)], [(false, true)]) := by
  unfold weightsHalves unitsReached
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

/-- At whatever layout the call returns. -/
theorem weights_full {Y : Model.WsLay}
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok Y) :
    weightsCovered (Plan.unitsOfLayout Y) keyFull.ranges.x = true := by
  have h := weightsB_full
  unfold weightsB at h
  rw [hY] at h
  exact h

/-- **THE CLAUSE "weights".** -/
theorem weights_ok {m : Made} {X : Source} (r1 : sourceOf m = .ok X)
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok m.p.X.layers.wsLay)
    (i2 : m.p.chains.key.oneTime.ranges = keyFull.ranges.x) :
    weightsCovered X.Y.units X.Y.k.oneTime.ranges = true := by
  unfold sourceOf at r1
  obtain ⟨D, _, r1⟩ := exc_bind r1
  dsimp only at r1
  obtain ⟨T, _, r1⟩ := exc_bind r1
  obtain rfl := Except.ok.inj r1
  show weightsCovered (Plan.unitsOfLayout m.p.X.layers.wsLay) m.p.chains.key.oneTime.ranges = true
  rw [i2]
  exact weights_full hY

end Johnson.KB9

#print axioms Johnson.KB9.weightsB_full
#print axioms Johnson.KB9.weightsB_rejects
#print axioms Johnson.KB9.weightsB_rejects_outside
#print axioms Johnson.KB9.halves_full
#print axioms Johnson.KB9.weights_full
#print axioms Johnson.KB9.weights_ok
