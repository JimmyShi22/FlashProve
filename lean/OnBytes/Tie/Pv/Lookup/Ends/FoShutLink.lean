-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoShutLink.lean.
In a run on a view, behind the chain's calls for a link's oracle messages no message of the prover
is open: SEND, the code switch, the frame's and the chain's first and later calls.

In the words of OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean, on the blocks' own bodies:
 * `dry_verify`, `dry_sendVerify`: SEND stays on the view, whether or not it closes the round of its
   answers; `shut_verify`, `shut_sendVerify`: with its own round of answers it leaves no message
   open.
 * `shut_switchVerify`, `shut_csSigmaVerify`: the code switch leaves no message open: SEND leaves
   the round of its answers open, the verifier's message with the positions closes it, and what
   follows (reading the old rows' openings, three notes, entering oracle messages and rows in the
   statement) leaves the channel's two marks alone.
 * `shut_first`, `shut_later`: `ReqFrame.first` (at the first link by SEND, from the second link on
   by the code switch) and `ReqFrame.later`.
 * `shut_checkFirst`, `shut_checkLater`: `ChainCheck.first` and `ChainCheck.later`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoShut

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem dry_verify (ids : Array Nat) (own : Bool) : Dry (Send.verify ids own) := by
  unfold Send.verify; dry
macro_rules | `(tactic| dry_atom) => `(tactic| exact dry_verify _ _)

theorem dry_sendVerify (n : Array OracleNotice) (own : Bool) : Dry (sendVerify n own) := by
  unfold sendVerify; dry
macro_rules | `(tactic| dry_atom) => `(tactic| exact dry_sendVerify _ _)

/-- Goes down a block written with do, through blocks that stay on the view, to the call that
closes the round of the answers; what follows that call is calm. -/
macro "shut_down" : tactic => `(tactic| repeat (first
  | intro _
  | (rw [if_pos rfl]; exact shut_closeEmpty _)
  | (refine Shut.before (by rw [if_pos rfl]; exact shut_closeEmpty _) ?_; intro _; calm; done)
  | (refine Shut.after (by dry) ?_)))

theorem shut_verify (ids : Array Nat) : Shut (Send.verify ids true) := by
  unfold Send.verify
  shut_down

theorem shut_sendVerify (n : Array OracleNotice) : Shut (sendVerify n true) := by
  unfold sendVerify
  refine Shut.after (by dry) fun ids => Shut.before (shut_verify ids) fun _ => ?_
  calm

theorem shut_switchVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) (withTheta : Bool) :
    Shut (switchVerify old T to others withTheta) := by
  unfold switchVerify
  refine Shut.after (by dry) fun S => Shut.after (by dry) fun _ => Shut.after (by dry) fun ids =>
    Shut.after (by dry) fun code => Shut.before (shut_closePositions _ _) fun drawn => ?_
  calm

theorem shut_csSigmaVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) : Shut (csSigmaVerify old T to others) := by
  unfold csSigmaVerify
  exact Shut.before (shut_switchVerify _ _ _ _ _) fun _ => Calm.pure _

theorem shut_later (f : ReqFrame) : Shut f.later := by
  unfold ReqFrame.later
  refine Shut.after (by dry) fun L => Shut.after (by dry) fun _ =>
    Shut.before (shut_sendVerify _) fun ids => ?_
  calm

theorem shut_checkLater (c : ChainCheck) : Shut c.later := by
  unfold ChainCheck.later
  refine Shut.after (by dry) fun _ => Shut.before (shut_later _) fun _ => ?_
  calm

theorem shut_first (f : ReqFrame) : Shut f.first := by
  unfold ReqFrame.first
  refine Shut.after (by dry) fun _ => Shut.after (by dry) fun L => Shut.after (by dry) fun G => ?_
  dsimp only
  refine Shut.after (by dry) fun f1 => Shut.after (by dry) fun plain => ?_
  dsimp only
  split <;> (refine Shut.after (by dry) fun _ => ?_) <;> split
  all_goals first
    | (refine Shut.before (shut_sendVerify _) fun ids => ?_; calm; done)
    | (refine Shut.before (shut_csSigmaVerify _ _ _ _) fun s => ?_; calm; done)

theorem shut_checkFirst (c : ChainCheck) : Shut c.first := by
  unfold ChainCheck.first
  refine Shut.after (by dry) fun _ => Shut.before (shut_first _) fun _ => ?_
  calm

end Fo
