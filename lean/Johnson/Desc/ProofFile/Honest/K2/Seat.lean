-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Seat.lean: WHERE EACH ORACLE MESSAGE OF THE SEGMENTS IS SENT: THE
ADDRESSES (`MsgAddr`, Honest/RowData.lean: the part that holds the sending, and the message's number
in that sending), BOTH WAYS, out of the plan's public data. For every caller of the frame's function
for the data of the segments' own messages, and for whoever fills it. Definitions with code; no
theorem. It imports no part, no half and no sending. Its tests stand in Honest/K2/ToyAddr.lean
[not in this library; so here read: not tested in this library].

  `sendersOf`     the places of a segment that hold a sending, in order
  `headCount`, `ownFirst`   how many messages stand in front of a segment's own in its first
                  sending (the carrying message and the copies); its own messages of moment 0
  `sentBy`        the oracle messages that a segment has sent, in the order of sending, but for what
                  rides at the start: the sender's address, the number in the sending, the notice,
                  the sending's number in the segment
  `addrIn`, `addrOf`   THE WAY FORTH: segment, the message's number in the segment's list ↦ address
  `seatOf`        THE WAY BACK: address ↦ segment, number: the first pair whose address it is
  `copyAddr`, `bearerOf`, `bearerAt`   a kept message that a switch sends anew: the copy's address;
                  the address of the message that bore it (`ReqGroup.born`, OnBytes/Iop/Req.lean);
                  the map from the one to the other, the identity elsewhere: for `RowData.comap`

The order in a switch's sending is the verifier's own (`switchNotices`,
Johnson/Top/H0/Tw/K2/Switch.lean, through `noticesAt`, Johnson/Desc/ProofFile/Lot/K2OfPlan.lean):
the carrying message; the kept members' copies; the next segment's own messages of moment 0; the
next fold's fresh mask. A message's number in its segment's list counts the own messages alone.
`addrIn`'s rule (head + m; one more behind the fresh mask) HANGS ON THE LIST's BEING BY MOMENT,
which is the plan's own test (`reqMomentsOk`, OnBytes/Iop/Req.lean); a kept message is of moment 0
(`reqMessageOk`, the same file).

Limits. The sender of a segment's moment t is taken to be the segment's place number t, from 0,
among its places of the kinds K1 and K2, and the sending to be part 0 of the row there: nothing here
holds that against a book. The switch behind the last segment stands at a place without a segment's
number: `sendersOf` does not find it, and `copyAddr` yields nothing there. That `seatOf` undoes
`addrOf` is tested at a toy, not proved: it hangs on no two messages having one address. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.RowData
import Johnson.Desc.ProofFile.Lot.K2OfPlan
import Johnson.Desc.ProofFile.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Place)

/-- The places of a segment that hold a sending, in order. -/
def sendersOf (sps : List Spot) (k : Nat) : List Place :=
  (sps.filter fun sp =>
    sp.place.link == some k && (sp.place.kind == .K1 || sp.place.kind == .K2)).map (·.place)

/-- How many messages stand in front of a segment's own in its first sending: the carrying message
and the copies; none at segment 0. -/
def headCount (f₀ : OnBytes.ReqFrame) (k : Nat) : Nat :=
  if k == 0 then 0 else 1 + (f₀.groups.getD k {}).target.kept.size

/-- A segment's own messages of moment 0: how many. -/
def ownFirst (f₀ : OnBytes.ReqFrame) (k : Nat) : Nat := ({ f₀ with link := k }.atMoment 0).length

/-- **The oracle messages that segment k has sent**, in the order of sending, but for what rides at
the start. f₀: a frame that holds the request's shape and its groups. -/
def sentBy (f₀ : OnBytes.ReqFrame) (sps : List Spot) (k : Nat) :
    List (Addr × Nat × OnBytes.OracleNotice × Nat) :=
  (sendersOf sps k).zipIdx.flatMap fun s =>
    ((P1K2.noticesAt f₀ k s.2).toList.zipIdx.filter fun n =>
        !(k == 0 && s.2 == 0 && decide (ownFirst f₀ k < n.2))).map fun n =>
      (⟨s.1, 0⟩, n.2, n.1, s.2)

/-- **The address of the own message number m of a segment**, out of the segment's messages in the
order of sending. head: how many stand in front of its own. own₀: its own messages of moment 0;
behind them stands the closing fold's fresh mask, then the later moments' messages. -/
def addrIn {α : Type} (sent : List (Addr × Nat × α)) (head own₀ m : Nat) : Option MsgAddr :=
  (sent[if m < own₀ then head + m else head + m + 1]?).map fun x => ⟨x.1, x.2.1⟩

/-- **THE WAY FORTH**: segment, the message's number in the segment's list. -/
def addrOf (f₀ : OnBytes.ReqFrame) (sps : List Spot) (k m : Nat) : Option MsgAddr :=
  addrIn (sentBy f₀ sps k) (headCount f₀ k) (ownFirst f₀ k) m

/-- **THE WAY BACK**: the first pair (segment, number in the segment's list) whose address this is.
Nothing at the address of a carrying message, a copy, a fresh mask, or of no message. -/
def seatOf (f₀ : OnBytes.ReqFrame) (sps : List Spot) (a : MsgAddr) : Option (Nat × Nat) :=
  f₀.shape.link.zipIdx.findSome? fun L =>
    (List.range L.1.messages.length).findSome? fun m =>
      if addrOf f₀ sps L.2 m == some a then some (L.2, m) else none

/-- The address of copy number i of the switch into segment l. -/
def copyAddr (sps : List Spot) (l i : Nat) : Option MsgAddr :=
  (sendersOf sps l).head?.map fun p => ⟨⟨p, 0⟩, 1 + i⟩

/-- The address of the message that bore copy number i of the switch into segment l. -/
def bearerOf (f₀ : OnBytes.ReqFrame) (sps : List Spot) (l i : Nat) : Option MsgAddr :=
  ((f₀.groups.getD l {}).born[i]?).bind fun b => addrOf f₀ sps b.1 b.2

/-- **A copy's address ↦ its bearer's; every other address ↦ itself.** Itself, too, IN SILENCE, at a
copy whose bearer has no address. -/
def bearerAt (f₀ : OnBytes.ReqFrame) (sps : List Spot) (a : MsgAddr) : MsgAddr :=
  ((List.range f₀.groups.size).findSome? fun l =>
    (List.range (f₀.groups.getD l {}).born.size).findSome? fun i =>
      if l != 0 && copyAddr sps l i == some a then bearerOf f₀ sps l i else none).getD a

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.sendersOf
#print axioms ProofFile.Honest.K2.headCount
#print axioms ProofFile.Honest.K2.ownFirst
#print axioms ProofFile.Honest.K2.sentBy
#print axioms ProofFile.Honest.K2.addrIn
#print axioms ProofFile.Honest.K2.addrOf
#print axioms ProofFile.Honest.K2.seatOf
#print axioms ProofFile.Honest.K2.copyAddr
#print axioms ProofFile.Honest.K2.bearerOf
#print axioms ProofFile.Honest.K2.bearerAt
