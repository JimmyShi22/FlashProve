-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoShut.lean.
The blocks of which the chain's calls for a link's oracle messages are made: which of them leave the
channel's two marks alone, which stay on the view, and which leave no message open.

A sub-proof's routine is run behind the chain's first call for its link (`ChainCheck.first`), and
goes on behind the chain's call at each later commitment (`ChainCheck.later`). Both receive the
roots of the prover's message, draw the seeds of the out-of-domain sample and receive the answers.
At the first link, and at a later commitment, the round of the answers is closed by itself. From the
second link on, the first call is a code switch: there the verifier's message with the positions
closes the round of the answers, and behind it the old rows' openings are read, notes are kept, and
oracle messages and rows are entered in the statement.

In the words of OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean:
 * the blocks that read or turn the statement, the book, the notes or the openings are `Calm`:
   `Blk.join`, `Blk.addRow`, `Blk.readOpened`, `Blk.receiveOracles`, `Send.admit`, `singleRowsRead`,
   `switchAdmit`, `ReqFrame.joinOwn` and those that they call;
 * receiving an element or an answer is `Dry`; `Blk.closeEmpty` and `Blk.closePositions` are `Shut`.
The chain's calls themselves stand in OnBytes/Tie/Pv/Lookup/Ends/FoShutLink.lean.

The tactics `calm` and `dry` take a block written with do apart by the rules; `calm_atom` and
`dry_atom` hold the blocks that are known by name and are extended as the file goes on.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoChan
import OnBytes.Model.ReqChain

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.PscRun

/-- A block that is known by name to be calm. -/
syntax "calm_atom" : tactic
macro_rules | `(tactic| calm_atom) => `(tactic| first
  | exact Calm.pure _ | exact calm_fail _ | exact calm_must _ _ | exact calm_test _ _
  | exact calm_check _ _ | exact calm_onView _ _ | exact calm_getOnView _ _ _
  | exact calm_testOnView _ _ | exact calm_checkOnView _ _ | exact calm_get _ _
  | exact calm_isDry | exact calm_samples | exact calm_firstTree | exact calm_lastEntry
  | exact calm_statement | exact calm_setStatement _ | exact calm_theBook | exact calm_setBook _
  | exact calm_onOracle _ _ | exact calm_onGroup _ _ | exact calm_requireRows _
  | exact calm_takeColumns _ _ | exact calm_note _ _ | exact calm_noteBy _ _
  | exact calm_recvRoot | assumption)

/-- Takes a block apart by the rules for calm blocks. -/
macro "calm" : tactic => `(tactic| repeat (first
  | calm_atom | intro _ | apply Calm.bind | apply Calm.loop | apply Calm.loopA | split))

/-- A block that is known by name to stay on the view. -/
syntax "dry_atom" : tactic
macro_rules | `(tactic| dry_atom) => `(tactic| first
  | exact Dry.pure _ | exact dry_item _ _ | exact (shut_close _ _ _).dry
  | (refine Calm.dry ?_; calm_atom) | assumption)

/-- Takes a block apart by the rules for blocks that stay on the view. -/
macro "dry" : tactic => `(tactic| repeat (first
  | dry_atom | intro _ | apply Dry.bind | apply Dry.loop | apply Dry.loopA | split))

/-! ### the statement, the book, the openings -/

theorem calm_oracle (o : Nat) : Calm (Blk.oracle o) := by unfold Blk.oracle; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_oracle _)
theorem calm_group (g : Nat) : Calm (Blk.group g) := by unfold Blk.group; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_group _)
theorem calm_newGroup (a b : Nat) : Calm (Blk.newGroup a b) := by unfold Blk.newGroup; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_newGroup _ _)
theorem calm_join (g o : Nat) (k : Bool) : Calm (Blk.join g o k) := by unfold Blk.join; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_join _ _ _)
theorem calm_closeLedger (o : Nat) : Calm (Blk.closeLedger o) := by unfold Blk.closeLedger; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_closeLedger _)
theorem calm_addRow (g : Nat) (row : Row) : Calm (Blk.addRow g row) := by unfold Blk.addRow; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_addRow _ _)
theorem calm_addRowsOnView (g : Nat) (rows : Unit → Option (List Row)) :
    Calm (Blk.addRowsOnView g rows) := by
  unfold Blk.addRowsOnView
  refine Calm.bind (calm_group _) fun _ => Calm.bind (calm_must _ _) fun _ =>
    Calm.bind (calm_getOnView _ _ _) fun l => Calm.forM _ (fun r => calm_addRow g r) l
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_addRowsOnView _ _)
theorem calm_countOpening (t : Nat) : Calm (Blk.countOpening t) := by
  unfold Blk.countOpening; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_countOpening _)

theorem calm_openTreesInto (B : TreeBook) (pos : Positions) :
    ∀ (ts : List Nat) (acc : Array (Nat × Array Nat × Array (Array F))),
      Calm (Blk.openTreesInto B pos ts acc)
  | [], acc => by unfold Blk.openTreesInto; calm
  | t :: ts, acc => by
    unfold Blk.openTreesInto
    have ih := calm_openTreesInto B pos ts
    refine Calm.bind (calm_countOpening _) fun _ => Calm.bind (calm_get _ _) fun _ =>
      Calm.bind (calm_must _ _) fun _ => Calm.bind (calm_takeColumns _ _) fun _ => ih _
theorem calm_openTrees (B : TreeBook) (pos : Positions) (ts : List Nat) :
    Calm (Blk.openTrees B pos ts) := calm_openTreesInto B pos ts #[]
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_openTrees _ _ _)
theorem calm_readOpened (ids : Array Nat) (pos : Positions) : Calm (Blk.readOpened ids pos) := by
  unfold Blk.readOpened; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_readOpened _ _)
theorem calm_receiveOracles (sent : Array OracleNotice) : Calm (Blk.receiveOracles sent) := by
  unfold Blk.receiveOracles; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_receiveOracles _)
theorem calm_admit (o : Nat) (rows : Array Row) : Calm (Send.admit o rows) := by
  unfold Send.admit; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_admit _ _)
theorem calm_singleRowsRead (s : SingleRows) (pos : Positions) :
    Calm (singleRowsRead s pos) := by unfold singleRowsRead; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_singleRowsRead _ _)
theorem calm_switchAdmit (old : SingleRows) (T : SwitchTarget) (to : Nat) (out : Switched)
    (y : Array E) : Calm (switchAdmit old T to out y) := by unfold switchAdmit; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_switchAdmit _ _ _ _ _)
theorem calm_joinOwn (f : ReqFrame) (sent : List Params.ReqMessage) (ids : Array Nat) :
    Calm (f.joinOwn sent ids) := by unfold ReqFrame.joinOwn; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_joinOwn _ _ _)
theorem calm_beginLink (f : ReqFrame) : Calm f.beginLink := by unfold ReqFrame.beginLink; calm
macro_rules | `(tactic| calm_atom) => `(tactic| exact calm_beginLink _)

/-! ### receiving and closing -/

theorem dry_recvE : Dry Blk.recvE := by unfold Blk.recvE; dry
macro_rules | `(tactic| dry_atom) => `(tactic| exact dry_recvE)
theorem dry_recvAnswer : Dry Blk.recvAnswer := by unfold Blk.recvAnswer; dry
macro_rules | `(tactic| dry_atom) => `(tactic| exact dry_recvAnswer)
theorem dry_recvEsInto : ∀ (n : Nat) (acc : Array E), Dry (Blk.recvEsInto n acc)
  | 0, acc => by unfold Blk.recvEsInto; dry
  | n + 1, acc => by
    unfold Blk.recvEsInto
    exact Dry.bind dry_recvE fun _ => dry_recvEsInto n _
theorem dry_recvEs (n : Nat) : Dry (Blk.recvEs n) := by
  unfold Blk.recvEs
  exact Dry.bind (dry_recvEsInto n _) fun _ => Dry.pure _
macro_rules | `(tactic| dry_atom) => `(tactic| exact dry_recvEs _)

theorem shut_closeEmpty (name : String) : Shut (Blk.closeEmpty name) := by
  unfold Blk.closeEmpty
  exact Shut.before (shut_close _ _ _) fun _ => Calm.pure _
macro_rules | `(tactic| dry_atom) => `(tactic| exact (shut_closeEmpty _).dry)
theorem shut_closePositions (name : String) (logN : Nat) :
    Shut (Blk.closePositions name logN) := by
  unfold Blk.closePositions
  refine Shut.before (shut_close _ _ _) fun _ => ?_
  calm
macro_rules | `(tactic| dry_atom) => `(tactic| exact (shut_closePositions _ _).dry)

end Fo
