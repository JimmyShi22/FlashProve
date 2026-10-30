-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/FoldFacts.lean: THE FACTS ON THE VERIFIER's STATE THAT THE LAWS TAKE FROM
"REACHED": one structure, a field a fact. STATEMENTS ALONE: nothing is proved here. A file BESIDE
the table of joints: it turns nothing of it.

Why. Some facts on the verifier's state hold along the whole run: they are laid at the start, or by
one sort of step, and every other step leaves them. As public items of the table's promise each has
to be kept by every sub-protocol's law. Since the promise at a border may have beside it a condition
Rch k that every accepting step hands on (Johnson/Desc/Sound/ChainOfPromisesR.lean), meant: "this
state is what the sub-protocols in front made, from the state at the start of this public part, of
some rounds and columns", such a fact wants ONE induction along the run instead. A law that spends
one takes this structure as a premise. THE LIST IS CLOSED AND IS TO SHRINK: a field is paid when it
is a theorem at the meant Rch.

What is said. `FoldData`: the public numbers that the tests read. `FoldFacts Rch at_ d reqW links
ps`: for every border k and every statement a with Rch k a whose state bears no mark, at s := (at_
a).2, each test in its own kind's text; eleven are equations (and `frameIs` is five), written out
(of these "groupIs" restates two kinds' tests in plain terms of the state: the bridge to each is
that kind's):
  bookInOrder   as many roots as trees; the tree at place z of the book bears the number ft + z
  seatsCarried  the book's places are the listed seats, as far as the book goes
  bookFits      every place of the book names a tree and a part that the book holds
  msgShapes     the statement's oracle messages' shapes are the listed ones, as far as they go
  weightsOk     every pending row's weights are well formed
  pileMasks · pileWithin · oneRow   the last sub-protocols' three tests on the pending rows and the
                ledgers of mask entries
  tidy          the statement is tidy
  codes · shape · layout            the statement's codes, the chain's own copy's frame's shape and
                rows' layout are the public parameters'
  liveShape · liveLayout            the like of the copy in use
  groups · liveGroups               both copies' frames' groups are those of their own shape
  frameShape · frameGroups          the like of the frame that the calls turn (`S.frame`: in the
                output head's front and in the finish a third copy, which moves alone there)
  ownIs         in front of a lookup in segment l: the five that the lookup reads off the state
                (codes, shape, layout, the segment's number, its list of arrays) are the public ones
  groupIs       in front of a sub-protocol of segment m, where a segment's own copy is in use: the
                group on which that copy lays its rows, and its frame's group, is the listed one
  frameIs       in front of a sub-protocol of segment m at piece j, a segment's own copy in use: its
                frame's moment is `momentAt` of j; its own oracle messages sent so far, and the kept
                ones of earlier segments, bear the listed numbers; and up to the closing (j ≤ 11, at
                the output head 13) its link is m and a later moment or the closing comes next
  rowsSent      the rows that the last closing has returned (in the frame of the copy in use;
                between two segments: the chain's own) name oracle messages for which the book has
                a place
  reqIs         the state's request's words are the public part's
  replyNat      a reply that the state holds is a number: its first coordinate alone bears it
  room          in front of a sub-protocol of segment m at piece 2 or behind: the index masks'
                ledger is not closed and has just free0 less the bearing segments in front of m
                left.
  roomEarly     the like at pieces 0 and 1 of a segment behind the first.

WHICH FACT HAS A FIELD. One that files of another kind than its own spend. A fact that only its own
kind's laws spend is a lemma of that kind's files over Rch: it needs no field.

(The letter "links" is read by `frameIs` alone: for the output head's shift.)

Limits. (1) STATEMENTS ALONE. At Rch := never every field is free. (2) THE WITNESSES INSIDE Rch
("there are rounds and columns") ARE NOT THE RUN's OWN: a law that spends a field may conclude
nothing on the run's transcript from them. (3) Each field is fenced to a state without a mark. (4)
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.First.Pend.WeightsB
import Johnson.Desc.K13.PubK13
import Johnson.Desc.Means.TestsBack
import Johnson.Top.H0.Walk.FrameEntriesDefs
import Johnson.Desc.First.Look.K3CallerOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

/-- The public numbers that the tests read. -/
structure FoldData where
  /-- the first tree's number -/
  ft : Nat
  /-- the listed seats and trees' shapes of the chain -/
  L : K12.Door.Laid
  /-- the listed shapes of the chain's oracle messages -/
  M : List OracleShape
  /-- the first chain's codes, the request's shape and layout, the segments' lists of arrays -/
  sent : Look.Sent
  /-- segment by segment: the number of its group in the statement -/
  groupAt : Nat → Nat
  /-- segment m, moment t: the numbers in the statement of m's own oracle messages of the moments
  below t -/
  ownAt : Nat → Nat → Array Nat
  /-- segment m: the numbers of the kept oracle messages of earlier segments as they are in m -/
  keptAt : Nat → Array Nat
  /-- how many entries the index masks' fresh ledger has -/
  free0 : Nat
  /-- segment by segment: it leaves a row on the committed table -/
  fvs : List Bool

/-- The next moment of a segment's frame, in front of the sub-protocol at piece j; o: the output
head's shift. -/
def momentAt (o j : Nat) : Nat := if j ≤ 4 + o then 1 else if j ≤ 6 + o then 2 else 3

/-- The output head's shift: 1 at that segment, else 0. -/
def shiftAt (links : List ModelPart) (m : Nat) : Nat := if links[m]? == some ModelPart.head then 1 else 0

/-- **The facts that the laws take from "reached".** at_: the public part and the verifier's state
of a statement. -/
structure FoldFacts {X P : Type} (Rch : Nat → X → Prop) (at_ : X → P × S) (d : FoldData)
    (reqW : P → Array UInt32) (links : List ModelPart) (ps : List Place) : Prop where
  bookInOrder : ∀ k a, Rch k a → (at_ a).2.failed = none →
    K12.Door.atFirstBook d.ft (at_ a).2 = true
  seatsCarried : ∀ k a, Rch k a → (at_ a).2.failed = none →
    K12.Door.atFirstSeats d.L (at_ a).2 = true
  bookFits : ∀ k a, Rch k a → (at_ a).2.failed = none → K12.Door.atFirstFits (at_ a).2 = true
  msgShapes : ∀ k a, Rch k a → (at_ a).2.failed = none →
    K12.Door.atFirstShapes d.M (at_ a).2 = true
  weightsOk : ∀ k a, Rch k a → (at_ a).2.failed = none → weightsB (at_ a).2 = true
  pileMasks : ∀ k a, Rch k a → (at_ a).2.failed = none → K13.pileMasksC (at_ a).2 = true
  pileWithin : ∀ k a, Rch k a → (at_ a).2.failed = none → K13.pileWithinC (at_ a).2 = true
  oneRow : ∀ k a, Rch k a → (at_ a).2.failed = none → K13.oneRowC (at_ a).2 = true
  tidy : ∀ k a, Rch k a → (at_ a).2.failed = none → OnBytes.Means.tidy4B (at_ a).2.st = true
  codes : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.st.codes = d.sent.codes
  shape : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.check.frame.shape = d.sent.shape
  layout : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.check.rows.layout = d.sent.layout
  liveShape : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.live.frame.shape = d.sent.shape
  liveLayout : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.live.rows.layout = d.sent.layout
  groups : ∀ k a, Rch k a → (at_ a).2.failed = none →
    (at_ a).2.check.frame.groups = reqGroups (at_ a).2.check.frame.shape
  liveGroups : ∀ k a, Rch k a → (at_ a).2.failed = none →
    (at_ a).2.live.frame.groups = reqGroups (at_ a).2.live.frame.shape
  frameShape : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.frame.shape = d.sent.shape
  frameGroups : ∀ k a, Rch k a → (at_ a).2.failed = none →
    (at_ a).2.frame.groups = reqGroups (at_ a).2.frame.shape
  ownIs : ∀ k a p l, Rch k a → (at_ a).2.failed = none → ps[k]? = some p → p.kind = .K3 →
    p.link = some l → Look.OwnIs d.sent l (at_ a).2
  groupIs : ∀ k a p m L, Rch k a → (at_ a).2.failed = none → ps[k]? = some p → p.link = some m →
    (at_ a).2.link? = some L → L.check.group = d.groupAt m ∧ L.check.frame.group = d.groupAt m
  frameIs : ∀ k a p m L, Rch k a → (at_ a).2.failed = none → ps[k]? = some p → p.link = some m →
    (at_ a).2.link? = some L →
    L.check.frame.moment = momentAt (shiftAt links m) p.piece ∧
      L.check.frame.own = d.ownAt m (momentAt (shiftAt links m) p.piece) ∧
      L.check.frame.keptBefore = d.keptAt m ∧
      (p.piece ≤ 11 + 2 * shiftAt links m →
        L.check.frame.link = m ∧ L.check.frame.next = .laterOrClose)
  rowsSent : ∀ k a, Rch k a → (at_ a).2.failed = none →
    ∀ o ∈ OnBytes.singleRowsOracles (at_ a).2.live.frame.rows, o < (at_ a).2.book.place.size
  reqIs : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.req = reqW (at_ a).1
  replyNat : ∀ k a, Rch k a → (at_ a).2.failed = none → ∀ g, (at_ a).2.out.reply = some g →
    OnBytes.Model.ofNat g.c0.toNat = g
  room : ∀ k a p m, Rch k a → (at_ a).2.failed = none → ps[k]? = some p → p.link = some m →
    2 ≤ p.piece → Johnson.Desc.First.Walk.Tied.roomIsB d.free0 d.fvs m (at_ a).2 = true
  roomEarly : ∀ k a p m, Rch k a → (at_ a).2.failed = none → ps[k]? = some p → p.link = some m →
    p.piece < 2 → 0 < m → Johnson.Desc.First.Walk.Tied.roomIsB d.free0 d.fvs m (at_ a).2 = true

end VerifiableInference.Desc.First
