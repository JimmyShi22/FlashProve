-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyRest.lean.
WHAT IT DOES NOT SHOW. No soundness. NO NEW FACT ON THE NEXT TOKEN's BLOCK: reply_rest is the record
behind its yes, as Law/ReplyPins.lean's reply_record writes it out, READ FIELD BY FIELD. IT SPEAKS
OF THE SEATED CONSTANT (the entry of the head's link, then the next token's block): what a block
that a chain joins behind it does to the record is not here (at the head's link that block is the
frame's "opened": the identity on the record, by a law in other files). That a description seats
this block: not here.
LETTERS. Under "there is" (place_rest): s0: pinned by the entry's yes from s.
OBJECT. Stored/ReplySeatAt.lean's blockAt | blockOf; Top/H0/Tw/K2C/Head.lean's headFrontQ.
USER. Whoever carries a sentence on the record past the next token's place: the promise's clauses on
the book, the statement's groups, the rows owed; the code switch's files' premise "the head's
part's frame is as the entry laid it".
WHAT IT IS. THE NEXT TOKEN's BLOCK TURNS THE REPLY's SEAT AND NOTHING ELSE OF THE RECORD; SO BEHIND
ITS WHOLE PLACE THE RECORD IS WHAT THE ENTRY OF THE HEAD's LINK LEFT, WITH A TOKEN LAID.
  reply_rest        behind a yes of the block: the statement, the book, the roots, the rows owed,
                    the mark, the state of the calls, the link's part ("here") and the request's
                    words are as they were; so are the two other fields of "out".
  place_rest        behind the entry and the block as one block: the entry's yes from s to s0, and
                    all these fields of the record behind are s0's.
  place_whole       with the code switch's files' laws on the entry (Top/H0/Tw/K2C/FrontGroup.lean:
                    headFrontQ_st | headFrontQ_rest): the statement has one fresh group more; the
                    book, the roots, the rows owed, the mark, the state of the calls and the
                    request's words are as IN FRONT OF THE PLACE.

-/
import Mathlib
import Johnson.Top.H0.Tw.K2C.FrontGroup
import Johnson.Desc.Kinds.Law.ReplyPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_st headFrontQ_rest withFresh)

/-- **The next token's block turns the reply's seat and nothing else.** -/
theorem reply_rest (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.roots = s.roots ∧ s'.rowsOwed = s.rowsOwed ∧
      s'.failed = s.failed ∧ s'.check = s.check ∧ s'.here = s.here ∧ s'.req = s.req ∧
      s'.out.indexMasks = s.out.indexMasks ∧ s'.out.pending = s.out.pending := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Came.reply_record l V hd
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Behind the entry and the block as one block. -/
theorem place_rest (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      ∃ s0, headFrontQ tl s = .ok s0 ∧ t.st = s0.st ∧ t.book = s0.book ∧ t.roots = s0.roots ∧
        t.rowsOwed = s0.rowsOwed ∧ t.failed = s0.failed ∧ t.check = s0.check ∧
        t.here = s0.here ∧ t.req = s0.req := by
  intro s rs gs t h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok t := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, _, _⟩ := reply_rest l W.hS.V h'
    exact ⟨s1, hfront _ _ _ _ hp, a1, a2, a3, a4, a5, a6, a7, a8⟩

/-- **The record behind the whole place, against the record in front of it.** -/
theorem place_whole (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      t.st = withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode ∧
        t.book = s.book ∧ t.roots = s.roots ∧ t.rowsOwed = s.rowsOwed ∧ t.failed = s.failed ∧
        t.check = s.check ∧ t.req = s.req := by
  intro s rs gs t h
  obtain ⟨s0, h0, a1, a2, a3, a4, a5, a6, _, a8⟩ := place_rest W l name front tl hfront s rs gs t h
  obtain ⟨b2, b3, b4, b5, b6, _, b8⟩ := headFrontQ_rest h0
  exact ⟨a1.trans (headFrontQ_st h0), a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5,
    a6.trans b6, a8.trans b8⟩

end VerifiableInference.Desc.Kinds.Head.Law
