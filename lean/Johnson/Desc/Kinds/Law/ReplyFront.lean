-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyFront.lean.
WHAT IT DOES NOT SHOW. No soundness. NOT THE CODE SWITCHING's FILES' ROW "carry m rides over
the next token's place": that row reads the two states through those files' way in (doorZ,
Top/H0/K2Caller/CarryClosed.lean), whose file does not lie beneath this one. This file says what
that row asks of it: what the front, the book and the roots are behind the
place. Nothing on whether the sentence "carry" holds. No example.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "The front"
(Top/H0/K2Hears/Long.lean: frontAt): what the code switching's sub-protocol is handed at a state, by
the sort of its place.
LETTERS. "There is" in place_front: s0: what the entry of the head's link makes of the state in
front: pinned by headFrontQ tl s = .ok s0.
OBJECT. The next token's own sub-protocol (Reply.blockAt), and the place "the entry of the head's
link, then the next token's" in Law/ReplyRest.lean's form.
USER. carryRow_reads (Top/H0/K2Caller/CarryReads.lean): its sentence
reads of the state the front, the book and the roots alone; and, through it, K6's and K7's files'
own debt that "carry 23" rides past the place (Law/K7AtMgAll.lean: K7Riders: carry).
WHAT IT IS. THE NEXT TOKEN's OWN SUB-PROTOCOL LEAVES THE FRONT, AT EVERY SORT OF PLACE; SO BEHIND
THE WHOLE PLACE THE FRONT, THE BOOK AND THE ROOTS ARE THOSE BEHIND THE ENTRY ALONE.
  reply_front       it writes the reply's seat alone (Law/ReplyPins.lean: Came.reply_record), which
                    the front does not read.
  place_front       at the place.
NEAREST RELATIVES: Law/ReplyRest.lean: reply_rest, place_rest: the same of the statement, the book,
the roots, the checks and where the chain stands, field by field: the front is made of three of
these; here it is said of the front itself, in the code switching's files' own word (frontAt).

-/
import Johnson.Desc.Kinds.Law.ReplyRest
import Johnson.Top.H0.K2Hears.Long

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ frontAt P2)

/-- **The next token's own sub-protocol leaves the front.** -/
theorem reply_front (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s')
    (p : P2) : frontAt p s' = frontAt p s := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Came.reply_record l V hd
  rfl

/-- **Behind the place the front, the book and the roots are those behind the entry alone.** -/
theorem place_front (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      ∃ s0, headFrontQ tl s = .ok s0 ∧ (∀ p, frontAt p t = frontAt p s0) ∧ t.book = s0.book ∧
        t.roots = s0.roots := by
  intro s rs gs t h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok t := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    obtain ⟨_, a2, a3, _⟩ := reply_rest l W.hS.V h'
    exact ⟨s1, hfront _ _ _ _ hp, fun p => reply_front l W.hS.V h' p, a2, a3⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.reply_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.place_front
