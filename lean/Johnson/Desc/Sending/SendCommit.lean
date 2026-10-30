-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sending/SendCommit.lean: a commitment of a link's sub-proof to further arrays (the
sending of the reads; of the digits), whole, as a plain function on data: the frame of a commitment
around the sending.

This file holds definitions only; no theorem is stated.

The program's routine is rootInH (OnBytes/Model/Trees.lean): two tests on the link's marks, the call
ChainCheck.later, then for each array named a test and a mark, and a count. All but the call is
Johnson/Top/H0/L3/Frame.lean's (commitFront, commitBehind, commitStep), which takes a sending as a
parameter. Here that parameter is filled.

Main names:
  reLoc.
  sendFor G p e₁ e₂: the later moment (chainLaterRow, Johnson/Desc/Sending/SendChain.lean) in the
    form of the frame's parameter: the walk's record, the sending's own state, its two rounds. The
    sending's own state is DState Unit: the statement, the book of trees, the roots' count, the
    opened columns.
  commitRow G p e₁ e₂ trees: L3.commitStep at it. commitD: the same at the description's ground
    (groundG, Johnson/Desc/Ground/Calls.lean).
  commitReads: the commitment to the reads at a layers' link and at the head's: the array's number
    is unwrapped first, as the program does in front of rootInH (OnBytes/Model/Layer.lean,
    Head.lean): refused where the list of arrays has none. (At an attention link the program takes
    the plan's number, 0 where there is none: OnBytes/Model/AttentionPlan.lean: no test there.)
  commitAsStep: in the one type of a step. It takes no column.
  sendD: a sending by itself at the description's ground.
  owed: see Johnson/Desc/Sending/Send.lean.

What is not claimed. That a test written here is the program's. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.Sending.SendChain
import Johnson.Top.H0.L3.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Send
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

/-- The state with other named values. -/
def reLoc {L M : Type} (d : DState L) (m : M) : DState M :=
  { st := d.st, book := d.book, roots := d.roots, opened := d.opened, loc := m }

/-- The later moment as the frame's parameter. -/
def sendFor (G : Ground ChainCheck) (p : GPar) (owed : Option Nat) (e₁ e₂ : Fmt.Entry) :
    L3.Send (DState Unit) :=
  fun c w rs =>
    match chainLaterRow G p owed id (fun _ x => x) e₁ e₂ (reLoc w c) rs w.opened with
    | some x => .ok (x.1.loc, reLoc x.1 ())
    | none => .error "the sending refuses"

/-- A commitment: two rounds. -/
def commitRow (G : Ground ChainCheck) (p : GPar) (owed : Option Nat) (e₁ e₂ : Fmt.Entry)
    (trees : List Nat) (s : L3.St (DState Unit)) (rs : List Fmt.RoundView) :
    Except String (L3.St (DState Unit)) :=
  L3.commitStep (sendFor G p owed e₁ e₂) trees s rs

/-- **A commitment at the description's ground.** -/
def commitD (p : GPar) (owed : Option Nat) (e₁ e₂ : Fmt.Entry) (trees : List Nat)
    (s : L3.St (DState Unit)) (rs : List Fmt.RoundView) : Except String (L3.St (DState Unit)) :=
  commitRow groundG p owed e₁ e₂ trees s rs

/-- **The commitment to the reads** where the program unwraps the array's number first. -/
def commitReads (p : GPar) (owed : Option Nat) (e₁ e₂ : Fmt.Entry) (reads : Option Nat)
    (s : L3.St (DState Unit)) (rs : List Fmt.RoundView) : Except String (L3.St (DState Unit)) :=
  match reads with
  | some t => commitD p owed e₁ e₂ [t] s rs
  | none => .error "the list of arrays has no array of the reads"

/-- In the one type of a step. -/
def commitAsStep (p : GPar) (owed : Option Nat) (e₁ e₂ : Fmt.Entry) (trees : List Nat) :
    L3.St (DState Unit) → List Fmt.RoundView → List (Nat × Nat × List UInt64) →
      Option (L3.St (DState Unit) × Nat) :=
  L3.asStep (commitD p owed e₁ e₂ trees)

/-- **The sending of W at the description's ground**, in the one type of a step. The chain's own
value here: the messages' numbers. -/
def sendD (p : GPar) (owed : Option Nat) (ns : Array OracleNotice) (e₁ e₂ : Fmt.Entry) :
    DState (Array Nat) → List Fmt.RoundView → List (Nat × Nat × List UInt64) →
      Option (DState (Array Nat) × Nat) :=
  sendRow groundG p owed ns (fun _ ids _ _ => ids) e₁ e₂

end VerifiableInference.Desc.First.Send
