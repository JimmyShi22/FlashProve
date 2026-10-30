-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyShape.lean.
WHAT IT DOES NOT SHOW. No soundness. ONE PREMISE OF ONE RULE ALONE: of the table's promise at the
border behind the next token's place it has the clause on the record's shape (shapeAt); the clauses
on the book, the statement's groups, what is held and what is public are not here. IT SPEAKS OF THE
SEATED CONSTANT STANDING ALONE (the entry of the head's link, then the next token's block): WHERE A
CHAIN JOINS A FURTHER BLOCK BEHIND IT, WHAT THAT BLOCK DOES TO THE RECORD IS NOT COVERED. That a
description seats this block: not here.
LETTERS. Under "there is" (front_record): a: pinned by s0.here = .head a.
OBJECT. Top/H0/Tw/K2C/Head.lean's headFrontQ (the step that enters the head's link), followed by
Stored/ReplySeatAt.lean's blockOf; Desc/First/Borders.lean's shapeAt (where the chain is to stand at
a border; no count of rows waits; no other link is open).
USER. The rule that carries the table's promise over a quiet row (its premise on the shape): at
every other quiet row the record's stand is as it was; at this one it turns from "between" to "the
head's front", so the premise is brought by hand.
WHAT IT IS. BEHIND THE NEXT TOKEN's PLACE THE RECORD STANDS AT THE HEAD's FRONT, NO LINK IS OPEN,
AND A COUNT OF ROWS WAITS JUST IF ONE WAITED IN FRONT: SO THE PROMISE's CLAUSE ON THE SHAPE RIDES
FROM THE BORDER IN FRONT OF THAT PLACE TO THE BORDER BEHIND IT.
  front_record      behind the entry's yes: the record stands in the head's link, not opened; the
                    count of rows owed is as it was. (Over headFrontQ_iff |
                    headFrontQ_tl, Top/H0/Tw/K2C/Asks.lean | HeadTl.lean.)
  front_stand       so: at the head's front; no link is open; "none waits" as in front.
  joined_stand      the same behind the entry and the next token's block as one block.
  shape_rides       the clause, from the border in front (piece 1 of a head's link) to the border
                    behind (piece 2).

-/
import Mathlib
import Johnson.Desc.First.Borders
import Johnson.Top.H0.Tw.K2C.HeadTl
import Johnson.Desc.Kinds.Law.ReplyPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S ModelPart Stand standOf standAt mayWait shapeAt)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_iff headFrontQ_tl)

/-- Behind the entry's yes. -/
theorem front_record {tl : HTailF2} {s s0 : S} (h : headFrontQ tl s = .ok s0) :
    (∃ a, s0.here = .head a ∧ a.opened = false) ∧ s0.rowsOwed = s.rowsOwed := by
  obtain ⟨a, ha, ho, _⟩ := headFrontQ_tl h
  refine ⟨⟨a, ha, ho⟩, ?_⟩
  obtain ⟨x, s₁, b, k⟩ := (headFrontQ_iff tl s s0).1 h
  have h0 : (s.enterHead tl).unmarked = .ok s₁ := k.enters
  have h1 := ((S.unmarked_ok _ _).1 h0).1
  rw [k.out, ← h1]
  simp [S.enterHead, k.between]

/-- So: at the head's front; no link is open; "none waits" as in front. -/
theorem front_stand {tl : HTailF2} {s s0 : S} (h : headFrontQ tl s = .ok s0) :
    standOf s0 = .headFront ∧ s0.link? = none ∧ s0.noneWaits = s.noneWaits := by
  obtain ⟨⟨a, ha, ho⟩, hr⟩ := front_record h
  refine ⟨?_, ?_, ?_⟩
  · unfold standOf S.inLink S.fork?
    rw [ha]
    simp [ho]
  · unfold S.link?
    rw [ha]
    simp [ho]
  · unfold S.noneWaits
    rw [hr]

/-- The same behind the entry and the next token's block as one block. -/
theorem joined_stand (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      standOf t = .headFront ∧ t.link? = none ∧ t.noneWaits = s.noneWaits := by
  intro s rs gs t h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok t := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    obtain ⟨_, _, _, _, _, _, rfl⟩ := Came.reply_record l W.hS.V h'
    have h3 : standOf s1 = .headFront ∧ s1.link? = none ∧ s1.noneWaits = s.noneWaits :=
      front_stand (hfront _ _ _ _ hp)
    exact h3

/-- **THE PROMISE's CLAUSE ON THE SHAPE RIDES OVER THE NEXT TOKEN's PLACE.** m: the head's link's
number; k1, k2: the kinds that the table's places bear (the clause reads neither). -/
theorem shape_rides (links : List ModelPart) (m : Nat) (hl : links[m]? = some .head) (k1 k2 : KindName)
    {s t : S} (hst : standOf t = .headFront ∧ t.link? = none ∧ t.noneWaits = s.noneWaits)
    (hs : shapeAt links (some ⟨1, some m, 1, k1⟩) s = true) :
    shapeAt links (some ⟨1, some m, 2, k2⟩) t = true := by
  obtain ⟨h1, h2, h3⟩ := hst
  have hw : s.noneWaits = true := by
    simp only [shapeAt, Bool.and_eq_true, Bool.or_eq_true] at hs
    rcases hs.1.2 with h | h
    · exact h
    · simp [mayWait, hl, VerifiableInference.Desc.First.kindsBeforeBatching] at h
  simp only [shapeAt, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨?_, Or.inl (h3.trans hw)⟩, ?_⟩
  · rw [h1]
    simp [standAt, hl]
  · rw [h2]
    rfl

end VerifiableInference.Desc.Kinds.Head.Law
