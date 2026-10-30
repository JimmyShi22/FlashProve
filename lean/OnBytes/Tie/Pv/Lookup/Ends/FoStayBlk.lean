-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStayBlk.lean.
A run on a view stays on the view: the blocks that a sub-proof's routines call on the chain.

`Dry` (OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean) of the blocks of OnBytes/Model/Rounds.lean by which a
sub-proof receives and
draws, of `Blk.takeMask`, `Blk.takeMasksInto`, `Blk.closeOne` and `foldRounds`, and of the chain's
closing of a link (`dry_checkClose`). Each is proved by the tactic `stays`
(OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the
block's own body; a block that is defined by recursion has a lemma by induction. The chain's first
and later calls have their statements in OnBytes/Tie/Pv/Lookup/Ends/FoShutLink.lean; here the tactic
is taught them.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStay

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible first
  | exact dry_recvE | exact dry_recvAnswer | exact dry_recvEs _
  | exact (shut_closeEmpty _).dry | exact (shut_closePositions _ _).dry
  | exact dry_verify _ _ | exact dry_sendVerify _ _
  | exact (shut_switchVerify _ _ _ _ _).dry | exact (shut_csSigmaVerify _ _ _ _).dry
  | exact (shut_first _).dry | exact (shut_later _).dry
  | exact (shut_checkFirst _).dry | exact (shut_checkLater _).dry
  | exact (calm_mustAs _ _).dry | exact (calm_testAs _ _).dry)

theorem dry_trReadLoop : ∀ (n : Nat) (a : Array E), Dry (trReadLoop n a)
  | 0, a => by
    rw [trReadLoop]
    exact Dry.pure a
  | n + 1, a => by
    rw [trReadLoop]
    exact Dry.bind dry_recvE fun _ => dry_trReadLoop n _
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact dry_trReadLoop _ _)

theorem dry_trRead (n : Nat) : Dry (trRead n) := by stays
theorem dry_trSum : Dry trSum := by stays
theorem dry_trAnswer (r : RoundName) : Dry (trAnswer r) := by stays
theorem dry_trAnswerNotZero (r : RoundName) : Dry (trAnswerNotZero r) := by stays
theorem dry_trEmpty (r : RoundName) : Dry (trEmpty r) := by stays
theorem dry_trPoint (r : RoundName) (n : Nat) : Dry (trPoint r n) := by stays
theorem dry_trBatchOpen : Dry trBatchOpen := by stays
theorem dry_trBatchRows (n : Nat) : Dry (trBatchRows n) := by stays
theorem dry_trBatch (n : Nat) : Dry (trBatch n) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible first
  | exact dry_trRead _ | exact dry_trSum | exact dry_trAnswer _ | exact dry_trAnswerNotZero _
  | exact dry_trEmpty _ | exact dry_trPoint _ _ | exact dry_trBatchOpen | exact dry_trBatchRows _
  | exact dry_trBatch _ | exact dry_trTrits _ _ | exact dry_closeAs _ _ _ _ _)

theorem dry_takeMask (o : Nat) : Dry (Blk.takeMask o) := by stays
theorem dry_takeMasksInto (o : Nat) : ∀ (n : Nat) (acc : Array Nat), Dry (Blk.takeMasksInto o n acc)
  | 0, acc => by
    rw [Blk.takeMasksInto]
    exact Dry.pure acc
  | n + 1, acc => by
    rw [Blk.takeMasksInto]
    exact Dry.bind (dry_takeMask o) fun _ => dry_takeMasksInto o n _

theorem dry_closeOne (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Dry (Blk.closeOne name kind nz) := by stays
theorem dry_foldRounds : ∀ (n : Nat) (claim : E), Dry (foldRounds n claim)
  | 0, claim => by
    rw [foldRounds]
    exact Dry.pure _
  | n + 1, claim => by
    rw [foldRounds]
    exact Dry.bind dry_recvE fun _ => Dry.bind dry_recvE fun _ =>
      Dry.bind (dry_closeOne _ _ _) fun _ => Dry.bind (dry_foldRounds n _) fun _ => Dry.pure _

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible first
  | exact dry_takeMask _ | exact dry_takeMasksInto _ _ _ | exact dry_closeOne _ _ _
  | exact dry_foldRounds _ _)

theorem dry_checkClose (k : ChainCheck) (q : ReqEquation) : Dry (k.close q) := by stays
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact dry_checkClose _ _)

end Fo
