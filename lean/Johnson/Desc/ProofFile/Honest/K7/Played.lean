-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7/Played.lean: WHAT THE NEXT TOKEN's HONEST ROW PLAYS, WRITTEN OUT,
AND HOW THE VERIFIER's TEXT READS IT. The row is one part with one move (`replyPart`,
Honest/K7.lean). Statements with proofs, by unfolding and by the library's laws on the two readings
of a field element (OnBytes/Slice/Field.lean).

  `asked_ok`        the asked token's three words are below the prime
  `asked_code`      THE CODING: the words that a view shows of the element sent, read back as the
                   verifier's text reads them, are the asked token:
                   `E.ofTriple (ofE (replyOf x)) = x.asked`
  `replyShown`      the one round as played
  `reply_played`    `playedRow` (Honest/Small/PlayRow.lean) at the row and one challenge is that
                   round, whatever rounds are shown and whatever columns are handed (`Seen`)
  `reply_state`     the input behind the row is the input in front
  `reply_read`      `readReply` (Johnson/Desc/Reply/ReplyStep.lean) of that round, at a challenge
                   that draws nothing, is the asked token

Limits. Nothing on whether the round is accepted. Nothing on a coin or a measure. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7
import Johnson.Desc.ProofFile.Honest.Small.PlayRow
import Johnson.Desc.Reply.ReplyStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)
open OnBytes.Desc.Reply (readReply)
open ProofFile.Honest.Small (playedRow stateRow)

variable {W₀ Rc Tr X : Type}

theorem asked_ok (x : Inst) : Fmt.Fld.two.okE x.asked.triple = true := by
  have h0 : Fmt.Fld.two.ok x.asked.triple.1 = true := Fmt.Fld.two.ok_red _
  have z : Fmt.Fld.two.ok 0 = true := by decide
  have h1 : Fmt.Fld.two.ok x.asked.triple.2.1 = true := z
  have h2 : Fmt.Fld.two.ok x.asked.triple.2.2 = true := z
  unfold Fmt.Fld.okE
  rw [h0, h1, h2]
  rfl

/-- **THE CODING.** -/
theorem asked_code (x : Inst) : OnBytes.E.ofTriple (OnBytes.Slice.ofE (replyOf x)) = x.asked := by
  have hk : Fmt.Fld.two.okE (OnBytes.Slice.ofE (replyOf x)) = true := by
    unfold Fmt.Fld.okE OnBytes.Slice.ofE
    rw [OnBytes.Slice.ok_ofF, OnBytes.Slice.ok_ofF, OnBytes.Slice.ok_ofF]
    rfl
  have e : OnBytes.Slice.ofE (replyOf x) = x.asked.triple :=
    OnBytes.Slice.toE_inj _ _ hk (asked_ok x) (OnBytes.Slice.toE_ofE _)
  rw [e]
  rfl

/-- The one round as played. -/
def replyShown (name : String) (a : Place) (x : Inst) (d : Fmt.Drawn) : Played :=
  ⟨name, a, 0, true, [.e (OnBytes.Slice.ofE (replyOf x))], [], d⟩

theorem reply_played (name : String) (a : Place)
    (c : RowCoins [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)])
    (t : State (Local W₀ Rc Inst Tr) X) (seen : Seen) (d : Fmt.Drawn) :
    playedRow name a [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)] 0 c t seen
      [d] = some [replyShown name a t.input.x d] := rfl

theorem reply_state (t : State (Local W₀ Rc Inst Tr) X) (d : Fmt.Drawn) :
    (stateRow [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)] t [d]).input =
      t.input := rfl

theorem reply_read (name : String) (a : Place) (x : Inst) :
    readReply ⟨(replyShown name a x ⟨[], [], [], none⟩).vals, ⟨[], [], [], none⟩⟩ =
      some x.asked := by
  show some (OnBytes.E.ofTriple (OnBytes.Slice.ofE (replyOf x))) = some x.asked
  rw [asked_code]

end ProofFile.Honest

#print axioms ProofFile.Honest.asked_ok
#print axioms ProofFile.Honest.asked_code
#print axioms ProofFile.Honest.reply_played
#print axioms ProofFile.Honest.reply_state
#print axioms ProofFile.Honest.reply_read
#print axioms ProofFile.Honest.replyShown
