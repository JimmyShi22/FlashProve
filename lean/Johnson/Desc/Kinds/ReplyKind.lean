-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/ReplyKind.lean: THE NEXT TOKEN, a kind of block of the protocol: what the format
of a block (Johnson/Desc/Block.lean) asks of it, made of the plain text of its part
(Johnson/Desc/Reply/ReplyStep.lean: readReply, isToken, stepReply, tokOf, replyGate, reqForm).
ReplyBlock.lean lays it into a Block. It shows nothing by itself. Definitions with code; no theorem.

WHAT IT IS FOR. The prover names the next token in the clear, in one round, before it commits to the
output head's cells. The head's claims use that token at the last position (Head.lean: y). At the
very end it is compared with the token that the client asks about. The block's whole worth is that
these three are ONE value: so there is ONE SEAT for the heard element in the carried record; this
block alone lays it; the head reads it there, through tokOf; the last test reads it there.
By itself the block says nothing of the model: that y is the top choice is the head's statement.
ROUNDS: one; the prover sends one element, not masked; nothing is drawn. READS: none. SENDS (the
honest prover): not written in this file (Johnson/Desc/ProofFile/Honest/K7.lean).

-/
import Johnson.Desc.Reply.ReplyStep
import Decl.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Reply

open OnBytes (E)
open OnBytes.Desc.Reply (readReply isToken tokOf replyGate reqForm)

/-- THE ONE SEAT: the element that was heard, if one was. -/
structure Seat (S : Type) where
  reply : S → Option E
  setReply : S → E → S

variable {S : Type}

/-- ROUNDS: the one round's entry of the plan: 24 bytes, no work, nothing drawn. -/
def rounds : List Fmt.DeclaredRound := [{ entry := { name := "REPLY", msg := 24 } }]

/-- DECIDES, each test under its name: one round; nothing has been heard yet; the round holds just
one element and draws nothing; the element is a token of a vocabulary of V: one coordinate, below V.
It is laid into the seat. -/
def decideE (V : Nat) (L : Seat S) (s : S) : List Fmt.RoundView → Except String S
  | [r] =>
    if (L.reply s).isSome then .error "heard once" else
    match readReply r with
    | none => .error "one element, nothing drawn"
    | some h => if isToken V h then .ok (L.setReply s h) else .error "a token"
  | _ => .error "one round"

/-- The same without the names. -/
def decide (V : Nat) (L : Seat S) (s : S) (rs : List Fmt.RoundView) : Option S :=
  (decideE V L s rs).toOption

/-- The token that the head reads: through tokOf and nothing else. -/
def token (L : Seat S) (s : S) : Option Nat := (L.reply s).map tokOf

/-- THE LAST TEST's part, when all blocks have run. asked: the client's token. A token was heard,
and it is asked; and where the last position is not checked (e < T), asked is 0. -/
def fin (V T r e asked : Nat) (L : Seat S) (s : S) : Bool :=
  replyGate V (L.reply s) asked && reqForm T r e asked

/-! ## Tests at a made-up record -/

/-- A record that is the seat alone. -/
def bare : Seat (Option E) := { reply := id, setReply := fun _ x => some x }
/-- A round that draws nothing. -/
def quiet (vals : List Fmt.ItemValue) : Fmt.RoundView := ⟨vals, ⟨[], [], [], none⟩⟩

-- The honest course: token 7 of 10 is heard, read by the head as 7, and asked.
#guard (decide 10 bare none [quiet [.e (7, 0, 0)]]).bind (token bare) == some 7
#guard ((decide 10 bare none [quiet [.e (7, 0, 0)]]).map (fin 10 64 60 64 7 bare)) == some true
-- Another token is asked: the last test says no.
#guard ((decide 10 bare none [quiet [.e (7, 0, 0)]]).map (fin 10 64 60 64 6 bare)) == some false
-- Heard twice: refused.
#guard (decide 10 bare (some (E.mk3 7 0 0)) [quiet [.e (7, 0, 0)]]).isNone
-- No token; no round; two rounds.
#guard (decide 10 bare none [quiet [.e (10, 0, 0)]]).isNone
#guard (decide 10 bare none [quiet [.e (7, 1, 0)]]).isNone
#guard (decide 10 bare none []).isNone
#guard (decide 10 bare none [quiet [.e (7, 0, 0)], quiet [.e (7, 0, 0)]]).isNone
-- Nothing heard: the last test says no, also at the token 0.
#guard !fin 10 64 15 47 0 bare none
-- The last position is not checked, and prover and client both say 1: the last test says no.
#guard ((decide 10 bare none [quiet [.e (1, 0, 0)]]).map (fin 10 64 15 47 1 bare)) == some false
#guard ((decide 10 bare none [quiet [.e (0, 0, 0)]]).map (fin 10 64 15 47 0 bare)) == some true

end VerifiableInference.Desc.Kinds.Reply
