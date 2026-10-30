-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/First.lean: the kind K1 at the first segment's opening: the chain's first two
rounds: the segment's cells' messages, its fold's fresh mask and the index-mask message go in one
prover's message; the sending is decideSend (Johnson/Desc/K1/Own.lean).

This file holds definitions only; no theorem is stated.

Written after the program's ChainCheck.first, ReqFrame.first and ReqFrame.joinOwn
(OnBytes/Model/ReqChain.lean, OnBytes/Iop/Req.lean), test by test:
  on the plan alone (firstPlanOk): the codes' lengths are lawful; the request's shape is lawful; its
    number of answers is the plan's samples; the layout is lawful. Three of the four stand in the
    description's own text: Own.lengthsFit (Johnson/Desc/Own/Lin.lean), Own.reqFits and
    Own.reqLayoutFits (Johnson/Desc/Own/Req.lean).
  the two entries' names, their draws other than 0 and rows = 0: by the make of ROUNDS
    (Johnson/Desc/K1/Send.lean writes the entries), held against the plan's by the fold's tests on
    the plan.
  what a round holds or draws: roundsFit, out of ROUNDS.
  on the carried record, and the joining: firstOwn, each refusal under its test's name.
  the sending itself: decideSend.

The record is the walk's state of the calls (ChainCheck) with its frame, as the program holds it: so
that the places behind, which read these records, find them by value.
Par.groups is filled: the segment's own sampled messages tell the group 0; the sampled messages at
the start tell the request's own group (ownGroup, Johnson/Desc/K1/Places.lean), which they join
behind the links; a message without a sample tells none. The group stands beside each part in one
list (firstLaid), of which both the parts and the groups are read. No theorem says that a message
joins the group that is told of it.

Main names: frame₀, firstLaid, firstParts, firstPlanOk, firstOwn, firstPar, firstSegmentOpening.

Not here: the room for the index masks: the step without a round that enters the link: the link's
frame's.

What is not claimed. That a test written here is the program's. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Places
import Johnson.Desc.Own.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- The frame in front of the first segment, out of the shape alone. -/
def frame₀ (q : Params.First) : ReqFrame := { shape := q.shape, groups := reqGroups q.shape }

/-- What the first prover's message holds, as named parts, in the order of sending; beside each part
the group that its sampled messages tell. -/
def firstLaid (q : Params.First) : List (String × Nat × Array OracleNotice) :=
  [("own", 0, ReqFrame.notices ((frame₀ q).atMoment 0)),
   ("the fold's mask", 0, #[foldMaskNotice ((frame₀ q).foldShape 0 {})]),
   ("at the start", ownGroup q, q.shape.atStart.toArray)]

/-- The named parts. -/
def firstParts (q : Params.First) : List (String × Array OracleNotice) :=
  (firstLaid q).map fun x => (x.1, x.2.2)

/-- On the plan alone. -/
def firstPlanOk (q : Params.First) (samples : Nat) : Bool :=
  Own.lengthsFit q.codes &&
    Own.reqFits q.codes q.shape &&
    q.shape.answers == samples &&
    Own.reqLayoutFits q.codes q.shape q.layout

/-- **The opening's decision** on the walk's state of the calls and the statement's part. -/
def firstOwn (P : Par) (owed : Option Nat) (c : ChainCheck) (d : DState Unit) (rs : List Fmt.RoundView) :
    Except String (ChainCheck × DState Unit) := do
  let f := c.frame
  -- on the carried record alone
  need "K1: a link is under way, or none is left" (!c.inLink && decide (c.link < c.links))
  need "K1: the frame awaits no first message" (f.next == .first)
  need "K1: the record does not stand at the first segment" (f.link == 0)
  let L ← named "K1: the segment is not in the shape" f.shape.link[f.link]?
  let _ ← named "K1: the segment has no group in the shape" f.groups[f.link]?
  let own := f.atMoment 0
  let others := ReqFrame.notices own ++ #[foldMaskNotice (f.foldShape f.link {})] ++
    f.shape.atStart.toArray
  need "K1: the record announces other messages than the block's rounds declare" (others == P.sent)
  let (g, d₁) ← named "K1: the group cannot be opened"
    (Ground.newGroupP d f.shape.code f.shape.maskCode)
  need "K1: the first segment has plain scalars" (L.plain == 0)
  let (ids, d₂) ← decideSend P owed d₁ rs
  need "K1: not a number for each message" (ids.size == others.size)
  let mask ← named "K1: the fold's mask has no number" ids[own.length]?
  let f₁ : ReqFrame := { f with
    group := g, moment := 1, own := #[], plain := [], keptBefore := f.keptBefore, mask := some mask,
    atStart := f.atStart ++ ids.extract (own.length + 1) ids.size }
  let mine := ids.extract 0 own.length
  let (f₂, d₃) ← named "K1: the joining refuses" (joinOwnP groundG P.gp d₂ f₁ own mine)
  pure ({ c with frame := { f₂ with next := .laterOrClose }, sent := mine, inLink := true,
                 moments := 1 }, d₃)

/-- The numbers of the first segment's opening. -/
def firstPar (q : Params.First) (gp : GPar) : Par :=
  { place := ⟨1, some 0, 1, .K1⟩, codes := q.codes, gp := gp, work := 0, parts := firstParts q
    groups := (firstLaid q).flatMap fun x => inGroup x.2.1 x.2.2 }

/-- **The first segment's opening, at S.** It stands between two links: it reads and writes the
walk's own state of the calls. -/
def firstSegmentOpening (q : Params.First) (gp : GPar) : Block S Cl :=
  let P : Par := firstPar q gp
  { name := "K1: the first segment's opening", place := P.place
    planOk := planOkOwn P && firstPlanOk q gp.samples
    rounds := rounds P, oracles := oracles P, before := before, claims := [], after := []
    decide := fun s rs _ => do
      need "K1: a link is open" s.atBetween
      let (c, d) ← firstOwn P (owedOf s) s.check (stateOf s ()) rs
      pure { laid s d with check := c } }

end VerifiableInference.Desc.K1
