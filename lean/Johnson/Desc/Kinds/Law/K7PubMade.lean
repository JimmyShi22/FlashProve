-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7PubMade.lean.
WHAT IT DOES NOT SHOW. No soundness. NOT THE WHOLE OF THE FIELD "pub" OF THE NEXT TOKEN's TIE's BILL
(Law/K7Seated.lean: K7Rest): of what that field asks (every public item that is open behind the
block holds of the record behind) this file has THE ONE ITEM THAT THE ROW MAKES; that the items
which ride past the block still hold is each filling's files' to say, at what the place turns (the
reply's seat; the link's part; one fresh group). IT SPEAKS OF THE SEATED CONSTANT (any block, then
the next token's).
LETTERS. No "there is". iU3: a letter of the output head's seat: the test does not read it.
OBJECT. The public item "a token is heard, and it is below the vocabulary's size" (Desc/First/
Borders.lean: Pub.tokenSmall: the next token's row makes it), as K6's and K7's layer of the filling
lays its Bool (Stored/FillK6K7.lean: tokenHeardB; fillK6K7_tokenSmall).
USER. The field "pub" at the next token's row; and whoever carries the item past a later block.
WHAT IT IS.
  token_made        BEHIND EVERY YES OF "ANY BLOCK, THEN THE NEXT TOKEN's" THE TEST SAYS YES.
  token_kept        the test reads the record through the reply's seat alone: a step that leaves
                    that seat leaves the test's answer.
  tokenSmall_made   the first, at the layer's field pub.
NEAREST RELATIVES: Law/FillK6K7Says.lean: tokenHeardB_says | tokenB_of_heard (what the test's yes
GIVES) · Law/AtBorder.lean: tokenB_small (a weaker test, which also says yes where nothing is heard)
· Law/ReplyHears.lean: joined_hears (called here).
A search (statements that name tokenHeardB, tokenB or the item, over the table's
files, the seats' files and K6's and K7's files, in versions other than these:
755 files): none concludes the test's yes from a block's.

-/
import Mathlib
import Johnson.Stored.FillK6K7
import Johnson.Desc.Kinds.Law.ReplyHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S Meaning)

/-- **BEHIND EVERY YES OF "ANY BLOCK, THEN THE NEXT TOKEN's" THE TEST SAYS YES.** -/
theorem token_made (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) (iU3 : Nat) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      tokenHeardB W.hS iU3 t = true := by
  intro s rs gs t h
  obtain ⟨y, hy, hlt⟩ := joined_hears W l name front s rs gs t h
  have e : Reply.token (seatAt W.hS iU3).toSeat t = some y := hy
  unfold tokenHeardB
  rw [e]
  exact decide_eq_true hlt

/-- The test reads the record through the reply's seat alone. -/
theorem token_kept (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s t : S)
    (e : t.out.reply = s.out.reply) : tokenHeardB h iU3 t = tokenHeardB h iU3 s := by
  have e' : Reply.token (seatAt h iU3).toSeat t = Reply.token (seatAt h iU3).toSeat s := by
    show t.out.reply.map OnBytes.Desc.Reply.tokOf = s.out.reply.map OnBytes.Desc.Reply.tokOf
    rw [e]
  unfold tokenHeardB
  rw [e']

/-- The first, at the layer's field pub. -/
theorem tokenSmall_made {P Wt : Type} (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) (iU3 mH : Nat) (Mg : Meaning P Wt) (z : P) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      (fillK6K7 W.hS iU3 mH Mg).pub .tokenSmall (z, t) = true := by
  intro s rs gs t h
  rw [fillK6K7_tokenSmall]
  exact token_made W l name front iU3 s rs gs t h

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.token_made
#print axioms VerifiableInference.Desc.Kinds.Head.Law.token_kept
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tokenSmall_made
