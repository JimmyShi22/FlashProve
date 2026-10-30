-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestHideOrder.lean: tests of the conditions by which OnBytes/Model/Hide.lean, Psc.lean
and Tsc.lean guard the order of their own steps. The tests run when this file compiles.

These conditions depend on public numbers and on the order of the calls, not on a value that a proof
file holds (the docstring of SubM in OnBytes/Model/Hide.lean names one exception). No theorem says
that no proof file can make one of them fail. They are tried here on small states that break one
condition each, most of them next to a control in which the same call goes through; Fork.hide,
Fork.shown and Fork.kapAt have no control of their own here. A #guard line sees only that a step
returns none or that the dry run fails, not which condition made it so. Where a condition has
several parts, the parts are broken one at a time.

Not every part is broken here. OnBytes/Model/TestPsc.lean breaks the other parts of Fork.hide and
Fork.shown, two more of Fork.pushEnt, and the condition of Fork.settleStep. Of the four parts of
Weight.fits (OnBytes/Iop/Psc.lean) only the length of psi is broken. Nothing checks that the
conditions tried are all that there are.

Four #guard lines have no control with the same entries: pscEnds without a scalar in Y, pscEnds
without an end value, levelIn with an empty order, and tscRounds with a point that is too short.
Their entries are meant to be those that the call would meet if its condition were not there. No
test here shows that they are, so such a line could also hold because the entries do not fit.

Not tested, because the condition can never be false: the sizes of what SubM.read has returned
(claimsIn, pscRound, pscEnds).

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Model.Tsc

namespace OnBytes.Model.TestHideOrder

open OnBytes.Psc (Weight)

/-- A small number as an element of the extension field. -/
def n (x : UInt64) : E := ofF x

/-- True if the dry run of x from the state F goes through against the plan's entries. -/
def runs {α : Type} (x : SubM α) (F : Fork) (entries : List Fmt.Entry) : Bool :=
  (Blk.rounds (x.run F) { entries := entries, st := {} }).isSome

/-! ## Hide.lean -/

/-- A state with one array of one virtual row with three columns, four slots, and theta = 2. -/
def small : Fork :=
  { (({ trees := #[{ K := 3, R := 1, rows := #[{ coef := #[oneE] }] }] } : Fork).fillL.slots 4) with
    theta := n 2, thetaDrawnF := true, planClaimsF := 2, kapMapF := #[false, false] }

/-- The state small with a virtual row whose weights begin at column 1. -/
def shifted : Fork :=
  { small with
    trees := #[{ K := 3, R := 1, rows := #[{ coef := #[oneE], L0 := 1, L := #[zeroE, zeroE] }] }] }

/-- A state with two slots, both filled: 1 - mask[0] and 2 - mask[1]. -/
def full : Fork :=
  (((({} : Fork).slots 2).hide 0 (n 1) oneE).bind (·.hide 1 (n 2) oneE)).getD {}

-- Fork.hide: the number of marks differs from the number of slots
#guard ((({ ns := 4, gotF := #[false] } : Fork).hide 0 (n 1) oneE).isNone)
-- Fork.shown: a filled mark outside the slots
#guard ((({ ns := 0, gotF := #[true], vp := #[n 5] } : Fork).shown 0).isNone)
-- Fork.pushEnt: an index below the first column that L holds
#guard ((shifted.lin (Aff.ent 0 0 0)).isNone)
-- Fork.pushEnt: an array that is not there; then a control: index 2 with L0 = 1 goes to L[idx - L0]
#guard ((small.lin (Aff.ent 1 0 0)).isNone)
#guard ((shifted.lin (Aff.ent 0 0 2)).map fun F => (F.trees.getD 0 {}).rows.map (·.L)) ==
  some #[#[n 0, n 1]]
-- Fork.pushSlot: the last slot, and the number after it
#guard ((small.lin (Aff.slot 3)).isSome && (small.lin (Aff.slot 4)).isNone)
-- Fork.push and Fork.kapTake once doorShutF is set
#guard ((small.push oneE {}).isSome && ({ small with doorShutF := true }.push oneE {}).isNone)
#guard ((small.kapTake 0).isSome && ({ small with doorShutF := true }.kapTake 0).isNone)
-- Fork.batchBy: theta is drawn once
#guard ((({} : Fork).batchBy (n 3)).isSome && (small.batchBy (n 3)).isNone)
-- Fork.kapAt: no weight before theta is drawn
#guard ((({} : Fork).kapAt 0).isNone)
-- Fork.kapTake: a claim outside the plan; fewer marks than claims; a weight taken twice
#guard ((small.kapTake 2).isNone)
#guard (({ small with kapMapF := #[false] }.kapTake 0).isNone)
#guard (((small.kapTake 0).bind (·.2.kapTake 0)).isNone)
-- Fork.kapAllTakenF: all taken; fewer marks than claims; one not taken
#guard ({ small with kapMapF := #[true, true] }.kapAllTakenF)
#guard (!{ small with kapMapF := #[true] }.kapAllTakenF)
#guard (!{ small with kapMapF := #[true, false] }.kapAllTakenF)
-- SubM.allTaken
#guard (runs SubM.allTaken { small with kapMapF := #[true, true] } [])
#guard (!runs SubM.allTaken small [])

-- Fork.settle: the control, then each of its seven conditions broken by itself
#guard ((full.settle 2).isSome)
#guard ((full.settle 3).isNone)
#guard (({ full with gotF := #[true, true, true] }.settle 2).isNone)
#guard (({ full with LS := #[] }.settle 2).isNone)
#guard (({ full with vp := #[] }.settle 2).isNone)
#guard (({ full with mf := #[] }.settle 2).isNone)
#guard (({ full with owed := #[{ what := "a claim" }] }.settle 2).isNone)
#guard (({ full with gotF := #[true, false] }.settle 2).isNone)
-- Fork.settle passes over slot 0, which has no coefficient: the claim is (slot 1) = 0
#guard (({ full with theta := n 2, thetaDrawnF := true }.lin (Aff.slot 1)).bind (·.settle 2)) ==
  some (#[zeroE, subE zeroE oneE], n 2)

/-! ## Psc.lean and Tsc.lean -/

/-- The plan's entry of the beginning of a sumcheck, with k scalars in the message. -/
def eEps (k : Nat) : Fmt.Entry := { name := "PSC epsilon", msg := 24 * k, drawE := 1 }

/-- The plan's entry of a round with two scalars. -/
def eRound : Fmt.Entry := { name := "PSC round", msg := 48, drawE := 1 }

/-- The plan's entry of the round in the further variable, with k scalars. -/
def eY (k : Nat) : Fmt.Entry := { name := "PSC Y", msg := 24 * k, drawE := 1, drawNZ := 1 }

/-- The plan's entry of the end values, k of them. -/
def eValues (k : Nat) : Fmt.Entry := { name := "PSC values", msg := 24 * k }

/-- The plan's entry of the draw on the line between a layer's two end values. -/
def eLine : Fmt.Entry := { name := "LINE", drawE := 1 }

/-- A state with eight free slots. -/
def eight : Fork := ({} : Fork).slots 8

-- RoundForm.weight: the degrees that the form nodes admits
#guard ((RoundForm.nodes.weight zeroE 0).isNone && (RoundForm.nodes.weight zeroE 1).isSome &&
  (RoundForm.nodes.weight zeroE 64).isSome && (RoundForm.nodes.weight zeroE 65).isNone)
-- weightHeld: the control; a wrong inverse; a psi whose sum is not 1
#guard (weightHeld (Weight.plain 3) && weightHeld (Weight.equality (n 5) 3))
#guard (!weightHeld { Weight.plain 3 with fixedInv := zeroE })
#guard (!weightHeld { Weight.plain 3 with psi := [] })
-- pscRound: the control; a weight that is not held; a weight whose sizes do not fit
#guard (runs (pscRound {} (Weight.plain 3) roundDraw) eight [eRound])
#guard (!runs (pscRound {} { Weight.plain 3 with fixedInv := zeroE } roundDraw) eight [eRound])
#guard (!runs (pscRound {} { Weight.plain 3 with psi := [zeroE, oneE, zeroE, zeroE] } roundDraw)
  eight [eRound])
-- roundIn: no round after the end
#guard (runs (roundIn .eq2 {}) eight [eRound])
#guard (!runs (roundIn .eq2 { ended := true }) eight [eRound])
-- pscEnds: the control; a second end; no scalar in Y; no end value
#guard (runs (pscEnds {} 2 2) eight [eY 2, eValues 2])
#guard (!runs (pscEnds { ended := true } 2 2) eight [eY 2, eValues 2])
#guard (!runs (pscEnds {} 0 2) eight [eY 0, eValues 2])
#guard (!runs (pscEnds {} 2 0) eight [eY 2, eValues 0])

/-- A sumcheck after one round in a variable with three coefficients. -/
def oneRound : Psc :=
  { started := true, vars := #[Weight.plain 3], r := #[n 2], first := 0, eps := n 4 }

-- pscRow: the control; a second claim; no start; no variable; a challenge is missing
#guard (runs (pscRow oneRound zeroE) eight [])
#guard (!runs (pscRow { oneRound with rowMade := true } zeroE) eight [])
#guard (!runs (pscRow { oneRound with started := false } zeroE) eight [])
#guard (!runs (pscRow { oneRound with vars := #[], r := #[] } zeroE) eight [])
#guard (!runs (pscRow { oneRound with r := #[] } zeroE) eight [])
-- Psc.rowForm: the kept terms enter with the factor eps
#guard ((oneRound.rowForm zeroE (Aff.slot 9)).slots.back? == some (9, n 4))

/-- The entries of a layer with one variable. -/
def layerEntries : List Fmt.Entry := [eEps 1, eRound, eY 2, eValues 2, eLine]

-- levelIn: the control; a variable outside; a point that is too short; an order that is too short
#guard (runs (levelIn 1 #[n 3] (Aff.ofConst (n 1)) [0]) eight layerEntries)
#guard (!runs (levelIn 1 #[n 3] (Aff.ofConst (n 1)) [1]) eight layerEntries)
#guard (!runs (levelIn 1 #[] (Aff.ofConst (n 1)) [0]) eight layerEntries)
#guard (!runs (levelIn 1 #[n 3] (Aff.ofConst (n 1)) []) eight [eEps 1, eY 2, eValues 2, eLine])
-- tscRounds: the control; a point that is too short
#guard (runs (tscRounds #[n 3] 1) eight [eEps 2, eRound])
#guard (!runs (tscRounds #[] 1) eight [eEps 2])

end OnBytes.Model.TestHideOrder
