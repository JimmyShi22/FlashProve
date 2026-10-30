-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysSteps.lean.
Routines of OnBytes/Model/Hide.lean and OnBytes/Model/Psc.lean stay on the view: those that are
named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStayBlk
import OnBytes.Model.Look

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-! ### the steps -/

theorem DryS.must (b : Bool) : DryS (SubM.must b) := by stays
theorem DryS.test (b : Bool) : DryS (SubM.test b) := by stays
theorem DryS.getO {α : Type} (x : Option α) : DryS (SubM.get x) := by stays
theorem DryS.read (n : ℕ) : DryS (SubM.read n) := by stays
theorem DryS.readSum : DryS SubM.readSum := by stays
theorem DryS.answer (r : RoundName) : DryS (SubM.answer r) := by stays
theorem DryS.answerNotZero (r : RoundName) : DryS (SubM.answerNotZero r) := by stays
theorem DryS.point (r : RoundName) (n : ℕ) : DryS (SubM.point r n) := by stays
theorem DryS.batch (n : ℕ) : DryS (SubM.batch n) := by stays
theorem DryS.batchOpen : DryS SubM.batchOpen := by stays
theorem DryS.batchRows (n : ℕ) : DryS (SubM.batchRows n) := by stays
theorem DryS.empty (r : RoundName) : DryS (SubM.empty r) := by stays
theorem DryS.trits (a b : ℕ) : DryS (SubM.trits a b) := by stays
theorem DryS.slot : DryS SubM.slot := by stays
theorem DryS.shown (j : ℕ) : DryS (SubM.shown j) := by stays
theorem DryS.publicPart (a : Aff) : DryS (SubM.publicPart a) := by stays
theorem DryS.claims : DryS SubM.claims := by stays
theorem DryS.allTaken : DryS SubM.allTaken := by stays
theorem DryS.settle (n : ℕ) : DryS (SubM.settle n) := by stays
theorem DryS.takeSlots (n : ℕ) : DryS (SubM.takeSlots n) := by stays
theorem DryS.hideRun (j : ℕ) (v : Array E) (f : E) :
    DryS (SubM.change (·.hideRun j v f)) := by stays
theorem DryS.push (w : E) (a : Aff) : DryS (SubM.push w a) := by stays
theorem DryS.lin (f : Aff) : DryS (SubM.lin f) := by stays
theorem DryS.kap : DryS SubM.kap := by stays
theorem DryS.batchBy (d : E) : DryS (SubM.batchBy d) := by stays
theorem DryS.setPlanClaims (n : ℕ) : DryS (SubM.setPlanClaims n) := by stays
theorem DryS.owe (s : String) : DryS (SubM.owe s) := by stays
theorem DryS.paid (i : ℕ) : DryS (SubM.paid i) := by stays
theorem DryS.rootTaken (t w : ℕ) : DryS (SubM.rootTaken t w) := by stays
theorem DryS.hide (j : ℕ) (y f : E) : DryS (SubM.hide j y f) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible first
  | exact DryS.must _ | exact DryS.test _ | exact DryS.getO _ | exact DryS.read _
  | exact DryS.readSum | exact DryS.answer _ | exact DryS.answerNotZero _
  | exact DryS.point _ _ | exact DryS.batch _ | exact DryS.batchOpen | exact DryS.batchRows _
  | exact DryS.empty _ | exact DryS.trits _ _ | exact DryS.slot | exact DryS.shown _
  | exact DryS.publicPart _ | exact DryS.claims | exact DryS.allTaken | exact DryS.settle _
  | exact DryS.takeSlots _ | exact DryS.hideRun _ _ _ | exact DryS.hide _ _ _
  | exact DryS.push _ _ | exact DryS.lin _ | exact DryS.kap | exact DryS.batchBy _
  | exact DryS.setPlanClaims _ | exact DryS.owe _ | exact DryS.paid _
  | exact DryS.rootTaken _ _)

/-! ### the sumcheck's routines -/

theorem DryS.claimsIn (n : ℕ) : DryS (SubM.claimsIn n) := by stays
theorem DryS.pscBeginAt (t : E) : DryS (pscBeginAt t) := by stays
theorem DryS.pscBegin (C : Aff) : DryS (pscBegin C) := by stays
theorem DryS.pscRound (p : Psc) (w : OnBytes.Psc.Weight) (d : Blk E) (hd : Dry d) :
    DryS (pscRound p w d) := by stays
theorem DryS.roundIn (f : RoundForm) (p : Psc) (z : E) (d : ℕ) : DryS (roundIn f p z d) := by
  stays
theorem DryS.pscEnds (p : Psc) (a b : ℕ) : DryS (pscEnds p a b) := by stays
theorem DryS.pscRow (p : Psc) (S0 : E) (k : Aff) : DryS (pscRow p S0 k) := by stays

end Fo
