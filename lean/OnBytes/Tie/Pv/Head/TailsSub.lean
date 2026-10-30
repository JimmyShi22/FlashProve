-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Head/TailsSub.lean: on a view, behind the lookup's routine, behind what the head's
check hears first and behind the merge's messages no message is open, whatever was open before.

Theorems with their proofs, and two tactics, by the laws of OnBytes/Tie/Pv/Keeps/KeepsTails.lean.
Each of these routines ends, as far as the channel goes, in the end values of a masked sumcheck
(`pscEnds`, OnBytes/Model/Psc.lean), whose last call on the channel closes a round in which nothing
is drawn; what follows that call leaves the channel as it was.

Main names:
  `leaves_take`, `pscRow_leaves`, `noteH_leaves`: three calls that leave the channel.
  `empty_ends`: behind the closing of a round in which nothing is drawn no message is open
    (`trEmpty_view`, OnBytes/Tie/Pv/Psc/PscView.lean).
  `pscEnds_ends`, `pad_ends`, `hearLogits_ends`, `hear_ends`, `wsForkMerge_ends`, `wsForkEnd_ends`:
    the routines are `EndsClean`.
  `leavesW`, `tailW`: the tactics leaves_ch and tail_walk of KeepsTails.lean with the three laws.

Limits: one direction: from a success. Nothing on a dry run. Nothing on which rounds are taken.


-/
import OnBytes.Tie.Pv.Keeps.KeepsTails
import OnBytes.Tie.Pv.Psc.PscView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.HeadLink
open OnBytes OnBytes.Model OnBytes.L5
open OnBytes.Tie.Pv.Keeps.Cut (EndsClean LeavesCh)

/-- A step on the state that returns a value leaves the channel. -/
theorem leaves_take {α : Type} (f : Fork → Option (α × Fork)) : LeavesCh (SubM.take f) :=
  fun s a s' h => by
    obtain ⟨F, c⟩ := s
    obtain ⟨G, c'⟩ := s'
    have h' : SubM.take f F c = .ok ((a, G), c') := h
    obtain ⟨y, -, e⟩ := (PscRun.take_ok f F c ((a, G), c')).1 h'
    have ec : c' = c := congrArg (fun z : (α × Fork) × Ctx => z.2) e
    show c'.ch = c.ch
    rw [ec]

/-- Behind the closing of a round in which nothing is drawn no message is open. -/
theorem empty_ends (r : RoundName) : EndsClean (SubM.empty r) := fun s a s' h d => by
  obtain ⟨F, c⟩ := s
  obtain ⟨G, c'⟩ := s'
  have h' : SubM.empty r F c = .ok ((a, G), c') := h
  obtain ⟨y, c1, hb, e⟩ := (PscRun.lift_ok (trEmpty r) F c ((a, G), c')).1 h'
  have ec : c' = c1 := congrArg (fun z : (Unit × Fork) × Ctx => z.2) e
  obtain ⟨_, _, _, _, _, _, _, k, _⟩ := PscRun.trEmpty_view r c c1 d hb
  show c'.ch.cur = none
  rw [ec]
  exact k.2

/-- Making a masked sumcheck's claim leaves the channel. -/
theorem pscRow_leaves (p : Psc) (S0 : E) (kept : Aff) : LeavesCh (pscRow p S0 kept) := by
  unfold pscRow
  leaves_ch

/-- A note of the head's check leaves the channel. -/
theorem noteH_leaves (what : String) (v : E) : LeavesCh (Head.noteH what v) := by
  unfold Head.noteH
  leaves_ch

/-- leaves_ch, with the three laws above. -/
macro "leavesW" : tactic =>
  `(tactic| repeat' first
      | exact pscRow_leaves _ _ _
      | exact noteH_leaves _ _
      | exact leaves_take _
      | exact LeavesCh.pure _
      | exact LeavesCh.ask _
      | exact LeavesCh.change _
      | exact LeavesCh.mustAs _ _
      | exact LeavesCh.subMust _
      | exact LeavesCh.same _
      | exact LeavesCh.fails _
      | refine LeavesCh.bind ?_ fun _ => ?_
      | refine LeavesCh.lift ?_
      | refine LeavesCh.up ?_
      | split
      | dsimp only)

/-- tail_walk, with leavesW. -/
macro "tailW " e:term : tactic =>
  `(tactic| repeat' first
      | with_reducible exact $e
      | with_reducible exact EndsClean.fails _
      | ((with_reducible refine EndsClean.andThen $e fun _ => ?_); leavesW; done)
      | refine EndsClean.behind (by keepsM) fun _ => ?_
      | split
      | dsimp only)

/-- Behind the end values of a masked sumcheck no message is open. -/
theorem pscEnds_ends (p : Psc) (degreeInY n : Nat) : EndsClean (pscEnds p degreeInY n) := by
  unfold pscEnds
  tailW (empty_ends _)

/-- Behind the lookup's messages no message is open. -/
theorem pad_ends (calls : Array Call) (pub : Array Nat) (lid : Nat) :
    EndsClean (Forest.pad calls pub lid) := by
  unfold Forest.pad
  tailW (pscEnds_ends _ _ _)

/-- Behind the last of the head's own sumchecks no message is open. -/
theorem hearLogits_ends (hS : Head.Shape) (lam : Nat) (zt : Array E) :
    EndsClean (Head.hearLogits hS lam zt) := by
  unfold Head.hearLogits
  tailW (pscEnds_ends _ _ _)

/-- Behind all that the head's check hears first no message is open. -/
theorem hear_ends (hS : Head.Shape) (Lh : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) : EndsClean (Head.hear hS Lh hp cov plain) := by
  unfold Head.hear
  tailW (hearLogits_ends _ _ _)

/-- Behind the merge's sumcheck no message is open. -/
theorem wsForkMerge_ends (lk : Nat) (sv : Array Nat) : EndsClean (wsForkMerge lk sv) := by
  unfold wsForkMerge
  tailW (pscEnds_ends _ _ _)

/-- Behind the merge's messages no message is open. -/
theorem wsForkEnd_ends (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    EndsClean (wsForkEnd lay cl sv) := by
  unfold wsForkEnd
  tailW (wsForkMerge_ends _ _)

end OnBytes.Tie.Pv.HeadLink

#print axioms OnBytes.Tie.Pv.HeadLink.pad_ends
#print axioms OnBytes.Tie.Pv.HeadLink.hear_ends
#print axioms OnBytes.Tie.Pv.HeadLink.wsForkEnd_ends
