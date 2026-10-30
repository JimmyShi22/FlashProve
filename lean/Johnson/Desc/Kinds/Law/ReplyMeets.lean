-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyMeets.lean.
WHAT IT DOES NOT SHOW. No soundness. That a description seats this block: not here. What the block
in front does to the record: not here (joined_meets hands its yes out as it is).
LETTERS. Under "there is" (joined_meets): s0: pinned by the front block's yes from s.
OBJECT. Stored/ReplySeatAt.lean's blockAt | blockOf: the next token's block as it is seated.
USER. The first sentence of the law on the next token (Law/K07Statement.lean), whose premise is a
yes of the kind's own decision (Desc/Kinds/ReplyKind.lean: decide) at a seat that was empty in
front.
WHAT IT IS. A YES OF THE SEATED BLOCK IS A YES OF THE KIND's OWN DECISION AT THE SEAT out.reply,
FROM THE SAME RECORD AT THE SAME ROUNDS TO THE SAME RECORD; AND THE SEAT WAS EMPTY IN FRONT.
  reply_meets       at blockAt.
  joined_meets      behind any block joined in front (Block.andThen), at blockOf: at the joined
                    block's own record and rounds.


A search (conclusions that name Reply.decide or decideE, over this library's
Kinds/ and Stored/): three laws on another form of the decision and one refusal; none of this shape.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReplyPins
import Johnson.Desc.Kinds.Law.ReplyHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- **A yes of the seated block is a yes of the kind's own decision; the seat was empty.** -/
theorem reply_meets (l V : Nat) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok t) :
    Reply.decide V Reply.seatAt s rs = some t ∧ s.out.reply = none := by
  obtain ⟨_, _, _, _, h0, _, _⟩ := Came.reply_record l V hd
  refine ⟨?_, h0⟩
  unfold Reply.blockAt Reply.entered at hd
  dsimp only at hd
  split at hd
  · split at hd
    · cases hd
    · have h : Reply.decideE V Reply.seatAt s rs = .ok t := hd
      unfold Reply.decide
      rw [h]
      rfl
  · cases hd

/-- **The same behind a block joined in front, AT THE JOINED BLOCK's OWN RECORD AND ROUNDS**: the
front block's yes leads from s to s0 on its own share of the rounds; the kind's own decision says
yes
from s0, on the rest of the rounds, to t. -/
theorem joined_meets (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) : ∀ s rs gs t,
    (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      ∃ s0, front.decide s (rs.take front.rounds.length) (gs.take front.openings) = .ok s0 ∧
        Reply.decide W.hS.V Reply.seatAt s0 (rs.drop front.rounds.length) = some t ∧
        s0.out.reply = none := by
  intro s rs gs t h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok t := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    exact ⟨s1, rfl, reply_meets l W.hS.V h'⟩

end VerifiableInference.Desc.Kinds.Head.Law
