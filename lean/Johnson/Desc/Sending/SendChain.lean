-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sending/SendChain.lean: a later moment as the sub-proofs' routines call it: one layer
above the frame's: after ChainCheck.later (OnBytes/Model/ReqChain.lean), a plain function on the
program's record ChainCheck.

This file holds definitions only; no theorem is stated.

Main names:
  chainLaterP: that layer's own test (a link is under way; a moment is due), then laterP
    (Johnson/Desc/Sending/Send.lean); the record takes the frame, the numbers sent and one moment
    more.
  chainLaterRow: the same in the one type of a step; get, put: where the chain's own values hold the
    record.

Not here: what rootInH (OnBytes/Model/Trees.lean) asks around this call of the link's and the
sub-proof's own states: Johnson/Top/H0/L3/Frame.lean has that.

What is not claimed. That a test written here is the program's. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.Sending.SendRow
import OnBytes.Model.ReqChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Send
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

variable {L : Type}

/-- The oracle messages of the present link's next moment, with their samples. -/
def chainLaterP (G : Ground L) (p : GPar) (d : DState L) (c : ChainCheck) (rs : List Fmt.RoundView) :
    Option (ChainCheck × DState L) :=
  if c.inLink && decide (c.moments < c.momentsDue) then
    (laterP G p d c.frame rs).map fun x =>
      ({ c with frame := x.1, sent := x.2.1, moments := c.moments + 1 }, x.2.2)
  else none

/-- The same as a step. -/
def chainLaterRow (G : Ground L) (p : GPar) (owed : Option Nat) (get : L → ChainCheck)
    (put : L → ChainCheck → L) (e₁ e₂ : Fmt.Entry) (d : DState L) (rs : List Fmt.RoundView)
    (_ : List (Nat × Nat × List UInt64)) :
    Option (DState L × Nat) :=
  let c := get d.loc
  (({ d := d, entries := [e₁, e₂], rounds := rs } : Mid L).send owed
    (ReqFrame.notices (c.frame.atMoment c.frame.moment)) fun d' rs' =>
      (chainLaterP G p d' c rs').map fun x => { x.2 with loc := put d.loc x.1 }).bind usedUp

end VerifiableInference.Desc.First.Send
