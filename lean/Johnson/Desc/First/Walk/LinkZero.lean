-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Walk/LinkZero.lean: the link's frame at link 0: what the program
`verify-on-bytes`'s walk over the first chain's links does itself between link 0's first call and
its sub-proof's first own round, as a plain function on data. It is the step of every other layers'
link (FirstQuiet.lean: layFirstQuiet) with one thing in front: the index-mask message is found and
its ledger's room is asked.
After that verifier's text: OnBytes/Model/StagesLinks.lean:534-541 (indexMasksH), :562-564;
Blk.oracle | Blk.get laid out on the statement's array of oracle messages.

  indexMasksAt room check os     the number of the index-mask message
     [I1] just one oracle message was sent at the chain's start and belongs to no link
          StagesLinks.lean:535-536 ("plan-link")
     [I2] it stands in the statement                                    :537 (Blk.oracle)
     [I3] it has a ledger                                               :538
     [I4] the ledger has room free entries (a closed ledger has none)   :539-540 ("plan-mask-row")
     room: a number of the plan: roomOf.
  roomOf fvs kCol     one entry for each sub-proof that leaves a row on the weight table, and the
     batching's 1 + 2 kCol if there is more than one row: written anew after StagesLinks.lean:306
     (onTable), :351 (indexMasksTaken), Iop/Batt.lean:58 (masksOf). fvs: for each link of the
     chain: does its record leave a row.
  layFirstQuietZero   the whole step: (e0) the message's number is laid into the walk's result;
     then front at link 0 [W1] [W2]; [G1]; [G2]; the fork, as at every layers' link

Order, as in that verifier: I1 ... I4, W1, W2, G1, G2.
Limits. No round, no column. No Blk, no Ctx, no SubM, no LinkM in any type of this file.
No soundness: definitions with code.

-/
import Johnson.Desc.First.Walk.FirstQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk
open OnBytes OnBytes.Model

/-- The entries that the request's rows on the weight table take from the index-mask message. -/
def roomOf (fvs : List Bool) (kCol : Nat) : Nat :=
  let rows := (fvs.filter id).length
  rows + (if rows > 1 then 1 + 2 * kCol else 0)

/-- **The index-mask message.** -/
def indexMasksAt (room : Nat) (check : ChainCheck) (os : Array Oracle) : Except String Nat :=
  if !(check.frame.atStart.size == 1) then .error
      "I1: plan-link: not just one message at the chain's start"
  else match check.frame.atStart[0]? with
    | none => .error "I1: plan-link: not just one message at the chain's start"
    | some im =>
      match os[im]? with
      | none => .error "I2: the index-mask message is not in the statement"
      | some x =>
        match x.ledger with
        | none => .error "I3: the index-mask message has no ledger"
        | some l =>
          if !decide (room ≤ (if l.closed then 0 else l.left)) then .error
              "I4: plan-mask-row: the ledger has too few free entries"
          else .ok im

/-- **«0.quiet» at link 0.** -/
def layFirstQuietZero (X : LinkPub) (p4 : Bool) (g : Nat) (Tp : Tail2) (Fp : Fork) (ns room : Nat)
    (check : ChainCheck)
    (out : Proof.LinksResult) (os : Array Oracle) : Except String LayStart :=
  match indexMasksAt room check os with
  | .error e => .error e
  | .ok im =>
    match front X 0 check { out with indexMasks := im } with
    | .error e => .error e
    | .ok (L, out) =>
      if !(L.link == (if p4 then 2 * g else g)) then .error
          "G1: internal-g-link: the link is not the group's"
      else if !(L.list.nt == Tp.nt && sizes X.Fp == sizes Fp) then .error
          "G2: the link's list or sizes are not the plan's"
      else .ok ⟨L, out, startFork X ns⟩

end Johnson.Desc.First.Walk
