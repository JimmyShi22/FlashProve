-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/SeatGuard.lean: a way to lay a chain so that a part that writes one seat of the carried
record, elsewhere than at the places told apart, is refused. Definitions alone; no theorem.

`same t s`: the seat is in s as it was in t. `but`: the test that tells apart the places at which a
block's own decision stands.
Main names:
  `sameBy h`: the test `same` that belongs to a reading h of the record: h s == h t.
  `atK7`: the test `but` "the place's kind is K7". Both stand here so that a description can take
    them without importing a file of laws.
  `seatSame`: the one test: the record behind a step, or the refusal "a block wrote a part of the
    record that it may not write".
  `Block.guarded`: that test behind the block's decision, behind each of its runs of claims and
    behind each of its runs behind the batching. At a place that `but` names the decision stands as
    it is; its runs are guarded there too.
  `Link.guarded`: lay, hear, batch, close, clear. `Chain.guarded`: first, front, links, back, last.
It turns no record: where it says yes, the record is the part's own.
The laws: Johnson/Desc/Sound/SeatGuardLaws.lean.

Limits. This file names no description. A guard can only refuse more.
(1) IT CAN REFUSE AN HONEST FILE. Where a text other than the one at the place told apart writes the
    seat on honest files, EVERY honest file is refused. So the guard lets honest files through only
    where the text at the place told apart is the one that writes the seat.
(2) `Block.guarded` READS THE BLOCK's OWN LABEL (`but b.place`). Whoever stamps places stamps first
    and guards then. Else a block that labels itself goes free elsewhere; and a block at the place
    told apart that bears another label (a joint takes its first block's) is guarded, so that every
    honest file is refused. Lay it as `(firstChain ..).map (Chain.guarded (sameBy h) but)`: then the
    laws hold of the text to the letter. Never lay it as `{ b.guarded .. with place := a }`.
(3) NEVER OVER AN OVERRULING, that is a lift that lays the seat back: there the guard sees the
    record put back and refuses nothing. Where a driver has such lifts, they are struck in the same
    turn in which the guard is laid: the guard never over such a lift, and such a lift never struck
    without the guard; else neither is done.
(4) h is the one seat's reply: the reading of K7's kind and of the last test: one term.
(5) What is joined into the block at the place told apart is free: it owes `Leaves` by name.
(6) The gate, which alone tells the idle form from the right one: each of the driver's plants on the
    reply ends in a refusal at the guarded chain, and one honest ride for each stored set of files
    ends honest.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- The guard's test that belongs to a reading h: h is behind the step as it was in front. -/
def sameBy {α : Type} [BEq α] (h : S → α) (t s : S) : Bool := h s == h t

/-- The place's kind is K7. -/
def atK7 (p : Place) : Bool := p.kind == .K7

/-- The record behind a step, if the seat is as it was in front; else a refusal. -/
def seatSame (same : S → S → Bool) (t s : S) : Except String S :=
  if same t s then .ok s
  else .error "a block wrote a part of the record that it may not write"

/-- **A block that may not write the seat**, but by its decision at a place that but names. -/
def Block.guarded (same : S → S → Bool) (but : Place → Bool) (b : Block S Cl) : Block S Cl :=
  { b with
    decide := fun t rs gs =>
      if but b.place then b.decide t rs gs else (b.decide t rs gs).bind (seatSame same t)
    claims := b.claims.map fun c =>
      (c.1, fun n t => (c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y)
    after := b.after.map fun c => (c.1, fun t => (c.2 t).bind (seatSame same t)) }

/-- The like for a link: its five parts that can write. -/
def Link.guarded (same : S → S → Bool) (but : Place → Bool) (L : Link S Cl) : Link S Cl :=
  { L with
    lay := fun t => (L.lay t).bind (seatSame same t)
    hear := L.hear.map (Block.guarded same but)
    batch := fun f => (L.batch f).guarded same but
    close := L.close.map (Block.guarded same but)
    clear := fun t => (L.clear t).bind (seatSame same t) }

/-- The like for a chain. -/
def Chain.guarded (same : S → S → Bool) (but : Place → Bool) (c : Chain S Cl) : Chain S Cl :=
  { first := c.first.guarded same but
    front := c.front.map (Block.guarded same but)
    links := c.links.map (Link.guarded same but)
    back := c.back.map (Block.guarded same but)
    last := c.last.guarded same but }

end VerifiableInference.Desc
