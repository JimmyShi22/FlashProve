-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Stored/ReplySeatAt.lean.
WHAT IT IS. The seat of the kind "the next token" (Desc/Kinds/ReplyKind.lean: Seat) at the first
chain's carried record (Desc/First/State.lean: S), a named test in front of the kind's decision, and
the kind's block there. A DESCRIPTION THAT SEATS blockOf RUNS THIS TEXT at the first place of the
head's link.
WHAT IT DOES NOT SHOW. Definitions, and one equation by rfl.
  seatAt     the seat at S: out.reply: THE ONE HOME OF THE HEARD REPLY: the output head's seat takes
             this seat by name (Stored/HeadSeatAt.lean: toSeat), and the last test reads the same
             field. It gives back what was laid AT EVERY RECORD (seatAt_law); it marks nothing.
  THAT JUST ONE PLAIN SCALAR WAS RECEIVED is the kind's own test ("one round"; "one element, nothing
             drawn": ReplyKind.lean: decideE): this block is the only one that asks it.
  entered    a named test of the seat's own, no part of the kind's text: the head's link is entered,
             and not yet opened: the block refuses by name at a record that stands at another place.
  blockAt, blockOf   the kind's block under that test; of the public record.

-/
import Johnson.Desc.First.State
import Johnson.Desc.Kinds.ReplyBlock
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Reply

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- **The seat at S**: out.reply. -/
def seatAt : Seat S where
  reply s := s.out.reply
  setReply s x := { s with out := { s.out with reply := some x } }

/-- The seat gives back what was laid, at every record. -/
theorem seatAt_law (s : S) (x : OnBytes.E) : seatAt.reply (seatAt.setReply s x) = some x := rfl

/-- A named test of the seat's own in front of a block's decision: the head's segment is entered,
and not yet opened. -/
def entered (b : Block S Unit) : Block S Unit :=
  { b with decide := fun s v g =>
      match s.here with
      | .head o =>
        if o.opened then .error "the next token: the head's link is not yet opened"
        else b.decide s v g
      | _ => .error "the next token: the head's link is entered" }

/-- **The kind's block at S**, under that test. -/
def blockAt (l V : Nat) : Block S Unit := entered (kind seatAt l 1 V)

/-- The same, of the public record. -/
def blockOf (W : OnBytes.Model.Verify.Public) (l : Nat) : Block S Unit := blockAt l W.hS.V

end VerifiableInference.Desc.Kinds.Reply
