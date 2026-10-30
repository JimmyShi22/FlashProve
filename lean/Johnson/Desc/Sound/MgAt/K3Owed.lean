-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Owed.lean: the kind "lookup" (K3): THE LEDGER WITHOUT ITS DOUBLE ENTRIES:
`K3OwedR`: what K03_law still owes at the composed meaning `mgAll Dm Mg`,
each debt ONCE. `K3RestR`
(Johnson/Desc/Sound/MgAt/K3Mean.lean) books some debts more than once, and some that are paid.

STRUCK, AND BY WHAT THEY ARE PAID:
  at the 24 calls' places in front of the head's (`AttRestR`, `LayRestR`: eight fields each): ownIn
    (the ledger's own fold.ownIs, with `IM.lookAt_link`) · fresh, pin, next (MgAt/K3Open.lean,
    MgAt/K3Pins.lean: by the kernel) · order (the ledger's hIn) · noState (its hd) · smpSt
    and, of sits, bySeat and smpIs (its es: the named reader of OOD samples): some, sent, fits stay;
  at the 25 digits' places (`DigRestR`: three fields): ownIn · hk1 · of sits, bySeat and smpIs;
  of the sentences on Dm: hS (it is hd's sentence);
  the letter nx (the place behind each lookup argument): it is `MgAt.nextOf`.

Main names: `AttOwedR` (29 fields), `LayOwedR` (27), `DigOwedR` (14) · `attRest_of_owed`,
`layRest_of_owed`, `digRest_of_owed` · `K3OwedR` · `k3Rest_of_owed`.

THE KEPT FIELDS' TEXTS ARE THE LOOKUP's FILES' OWN, LAID HERE BY A PROGRAM; Lean holds each
against its original in the three filling rules.

In `K3OwedR` idx IS A LETTER OF EACH SEGMENT (idx l in att and lay): with one idx for all 24
the structure is, by reading (no theorem), empty at the release's files:
see K3Mean.lean's head.

Limits: `K3OwedR` is a premise: shown at no Dm. Nothing on soundness by
itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAt.K3Mean

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V)
  (a a' : Desc.Place) (k l : ℕ) (x : Desc.First.Look.Place)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **What is owed at attention's calls, each debt once.** -/
structure AttOwedR (A : Attention.Shape) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
      Option ((attSg x Dm.sent Dm.rad3).om i).Smp)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle)) : Prop where
  /-- test: an attention link -/
  odd : l % 2 = 1
  /-- test; in the goals' scope a theorem (attAt_letters): the shape is the model's owner's -/
  shapeIs : A = Road.Hd.shapeA X (l / 2)
  /-- test; in the goals' scope a theorem (attAt_scope) -/
  cellsIn : planesInB x A tl = true
  /-- test; in the goals' scope a theorem (tabsAre_scope) -/
  tabs : TabsAre A x.fs
  /-- test; in the goals' scope a theorem (tabsAre_scope) -/
  room : ∀ c : Fin 4, (Road.L5.dimOf A).used c ≤ 2 ^ Cb.LdLkp.Port.nOf x.fs c
  /-- test: the segment stands in front of the head's -/
  hlt : l < 24
  /-- test -/
  hhd : l ≠ headLink X
  /-- test; in the goals' scope a theorem (attAt_letters, lay_letters): the approximate range
  proof's parameters are the model's owner's -/
  htl : tl = tls x.link
  /-- test on the public parameters and the layout -/
  tie : linkTieB X Dm.sent Dm.rad3 num idx x.link tl = true
  /-- test on the list of rounds: a member's number is its label's; no pad's place -/
  one : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id
  /-- test on the table's numbers: one tenant with that number; no pad's place -/
  own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N
  /-- test on the table's numbers -/
  seated : GroupsSeated Dm.ms Dm.N
  /-- test; in the goals' scope a theorem (fit_at_tlAt) -/
  fit : sizesFit X (fun j => szOf (tls j)) = true
  /-- test on the numbers and the piece: every sampled tenant that is open in front lies below -/
  base : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
    t.1 < q.base
  /-- test: the built segment's number of slots is the place's -/
  slots : (Dm.built[l]?).map (·.ns) = some (theP).ns
  /-- test on the table -/
  stand : sameStand linksFull a a' = true
  /-- test on the numbers -/
  book : bookFit Dm.N PS told = true
  /-- test on the numbers: this sub-protocol tells no tree -/
  tells : told[k]? = some []
  /-- test on the table and the meaning's list of extra public tests -/
  pubs : pubFit (mgAll Dm Mg).more linksFull PS = true
  /-- term: H reads a witness as hidAtSeat does (there: rfl, with seatsOf_all) -/
  hid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- term: the like for the part "small" -/
  small : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j
  /-- term: reader's and owner's readings agree at every witness (readsOne_readAt, WordsAtQ.lean) -/
  reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- accept: what the row opens says the kind's sentence on the objects -/
  objects : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    Desc.K3.k3OnOut theP v.1 = true →
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
    ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
    attObjects x A tl Dm.sent Dm.rad3 seatL Dm.arr
      (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w
  /-- accept: the other kinds' public tests that are open behind hold behind -/
  othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull a) ++
        pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
          (Desc.First.rowOf linksFull a)),
      p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true
  /-- accept: the like for the public sentences -/
  othersP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull a),
      p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1)
  /-- accept: every open item that the row does not close rides -/
  rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b'
  /-- test on the list of rounds: three of `ListSits` -/
  some : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨callsSending x Dm.sent Dm.rad3 seatL, i⟩
  sent : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
    Dm.seat3 x.link false i.1 ∈ Dm.N.sent l 0
  fits : Desc.Sound.SeatFits Dm.G Dm.sent.codes (sigListCalls Dm.sent Dm.rad3 x.link) seatL

/-- **What is owed at the layers' calls, each debt once.** -/
structure LayOwedR (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
      Option ((attSg x Dm.sent Dm.rad3).om i).Smp)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle)) : Prop where
  /-- test: a layers' link -/
  even : l % 2 = 0
  /-- test -/
  noAtt : attAt X l = none
  /-- test: profile 4: two links a group -/
  step : l / Desc.First.Look.stepOf X = l / 2
  /-- test: the segment stands in front of the head's -/
  hlt : l < 24
  /-- test -/
  hhd : l ≠ headLink X
  /-- test; in the goals' scope a theorem (attAt_letters, lay_letters): the approximate range
  proof's parameters are the model's owner's -/
  htl : tl = tls x.link
  /-- test on the public parameters and the layout -/
  tie : linkTieB X Dm.sent Dm.rad3 num idx x.link tl = true
  /-- test on the list of rounds: a member's number is its label's; no pad's place -/
  one : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id
  /-- test on the table's numbers: one tenant with that number; no pad's place -/
  own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N
  /-- test on the table's numbers -/
  seated : GroupsSeated Dm.ms Dm.N
  /-- test; in the goals' scope a theorem (fit_at_tlAt) -/
  fit : sizesFit X (fun j => szOf (tls j)) = true
  /-- test on the numbers and the piece: every sampled tenant that is open in front lies below -/
  base : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
    t.1 < q.base
  /-- test: the built segment's number of slots is the place's -/
  slots : (Dm.built[l]?).map (·.ns) = some (theP).ns
  /-- test on the table -/
  stand : sameStand linksFull a a' = true
  /-- test on the numbers -/
  book : bookFit Dm.N PS told = true
  /-- test on the numbers: this sub-protocol tells no tree -/
  tells : told[k]? = some []
  /-- test on the table and the meaning's list of extra public tests -/
  pubs : pubFit (mgAll Dm Mg).more linksFull PS = true
  /-- term: H reads a witness as hidAtSeat does (there: rfl, with seatsOf_all) -/
  hid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- term: the like for the part "small" -/
  small : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j
  /-- term: reader's and owner's readings agree at every witness (readsOne_readAt, WordsAtQ.lean) -/
  reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- accept: what the row opens says the kind's sentence on the objects -/
  objects : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    Desc.K3.k3OnOut theP v.1 = true →
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
    ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
    layObjects x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dm.sent Dm.rad3
      (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard v.1 w
  /-- accept: the other kinds' public tests that are open behind hold behind -/
  othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull a) ++
        pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
          (Desc.First.rowOf linksFull a)),
      p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true
  /-- accept: the like for the public sentences -/
  othersP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull a),
      p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1)
  /-- accept: every open item that the row does not close rides -/
  rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b'
  /-- test on the list of rounds: three of `ListSits` -/
  some : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨callsSending x Dm.sent Dm.rad3 seatL, i⟩
  sent : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
    Dm.seat3 x.link false i.1 ∈ Dm.N.sent l 0
  fits : Desc.Sound.SeatFits Dm.G Dm.sent.codes (sigListCalls Dm.sent Dm.rad3 x.link) seatL

variable {Dm Mg Rch claim num idx tls tok l x}

/-- **The lookups' authors' structure, from what is owed.** -/
theorem attRest_of_owed {seats : List (ℕ × ℕ)} (hM : Mg.more = {})
    (es : Dm.smp = smpNamed Dm.cs seats)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (hIn : InOrderReads Mg) (fold : K3Fold Rch Dm.sent)
    (hl : l < 25) (hlook : lookAt X l false = some x) {A : Attention.Shape} {tl : HTailF2}
    {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    {b' : Desc.Block Desc.First.S Cl} {told : List (List Desc.Oracle)}
    (W : AttOwedR Dm Mg Rch claim num idx tls tok (IM.k3Place l false) (MgAt.nextOf l false)
      (k3K l false) l x A tl (smpCalls seats Dm.sent Dm.rad3 Dm.seat3 x) q b' told) :
    AttRestR Dm Mg Rch claim num idx tls tok (IM.k3Place l false) (MgAt.nextOf l false)
      (k3K l false) l x A tl (smpCalls seats Dm.sent Dm.rad3 Dm.seat3 x) q b' told :=
  { odd := W.odd
    shapeIs := W.shapeIs
    cellsIn := W.cellsIn
    tabs := W.tabs
    room := W.room
    hlt := W.hlt
    hhd := W.hhd
    htl := W.htl
    tie := W.tie
    one := W.one
    own := W.own
    seated := W.seated
    fit := W.fit
    base := W.base
    slots := W.slots
    stand := W.stand
    book := W.book
    tells := W.tells
    pubs := W.pubs
    hid := W.hid
    small := W.small
    reads := W.reads
    objects := W.objects
    othersPub := W.othersPub
    othersP := W.othersP
    rides := W.rides
    sits := es ▸ listSits_named Dm.G x Dm.sent Dm.rad3 Dm.seat3 seats Dm.ms Dm.N l W.some W.sent
      W.fits
    pin := MgAt.pin_open_calls hl
    next := MgAt.next_place hl false
    fresh := by
      rw [mgAll_more_closed Dm Mg hM]
      exact (MgAt.k3_open_calls hl).2.2
    order := hIn
    smpSt := fun z s s' h => by
      rw [es]
      funext t i
      exact smpNamed_same Dm.cs seats (z, s) (z, s') h t i
    noState := fun c z s s' => hd c (z, s') (z, s) rfl
    ownIn := fun z u _ hr hu => by
      rw [IM.lookAt_link hlook]
      exact fold.ownIs l hl false ((z, u.1), u.2) hr hu }

/-- The like at the layers' calls. -/
theorem layRest_of_owed {seats : List (ℕ × ℕ)} (hM : Mg.more = {})
    (es : Dm.smp = smpNamed Dm.cs seats)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (hIn : InOrderReads Mg) (fold : K3Fold Rch Dm.sent)
    (hl : l < 25) (hlook : lookAt X l false = some x) {tl : HTailF2}
    {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    {b' : Desc.Block Desc.First.S Cl} {told : List (List Desc.Oracle)}
    (W : LayOwedR Dm Mg Rch claim num idx tls tok (IM.k3Place l false) (MgAt.nextOf l false)
      (k3K l false) l x tl (smpCalls seats Dm.sent Dm.rad3 Dm.seat3 x) q b' told) :
    LayRestR Dm Mg Rch claim num idx tls tok (IM.k3Place l false) (MgAt.nextOf l false)
      (k3K l false) l x tl (smpCalls seats Dm.sent Dm.rad3 Dm.seat3 x) q b' told :=
  { even := W.even
    noAtt := W.noAtt
    step := W.step
    hlt := W.hlt
    hhd := W.hhd
    htl := W.htl
    tie := W.tie
    one := W.one
    own := W.own
    seated := W.seated
    fit := W.fit
    base := W.base
    slots := W.slots
    stand := W.stand
    book := W.book
    tells := W.tells
    pubs := W.pubs
    hid := W.hid
    small := W.small
    reads := W.reads
    objects := W.objects
    othersPub := W.othersPub
    othersP := W.othersP
    rides := W.rides
    sits := es ▸ listSits_named Dm.G x Dm.sent Dm.rad3 Dm.seat3 seats Dm.ms Dm.N l W.some W.sent
      W.fits
    pin := MgAt.pin_open_calls hl
    next := MgAt.next_place hl false
    fresh := by
      rw [mgAll_more_closed Dm Mg hM]
      exact (MgAt.k3_open_calls hl).2.2
    order := hIn
    smpSt := fun z s s' h => by
      rw [es]
      funext t i
      exact smpNamed_same Dm.cs seats (z, s) (z, s') h t i
    noState := fun c z s s' => hd c (z, s') (z, s) rfl
    ownIn := fun z u _ hr hu => by
      rw [IM.lookAt_link hlook]
      exact fold.ownIs l hl false ((z, u.1), u.2) hr hu }

end

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (X : Verify.Public)
  (Dn : Desc.First.Look.Sent) (L : K3Letters Cells Tok) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl) (ms : List Mem)

local notation "WT" => Desc.Wit Cells Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
set_option quotPrecheck false in
local notation "PieceT" => Piece (ckP .two) Fr (P × Desc.First.S) Cl WT

/-- **What is owed at one digits' place, each debt once.** -/
structure DigOwedR (a a' : Desc.Place) (k l : ℕ) (sub : ModelPart) (x : Desc.First.Look.Place)
    (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dn L.rad).length) →
      Option ((digSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle)) : Prop where
  /-- a test on the table and the meaning's list of extra public tests -/
  hfit : pubFit Mg.more linksFull PS = true
  /-- a test on the table: the segment's three pins are open in front -/
  hOp : digitsOpenB linksFull PS k l = true
  /-- a test on the table -/
  hfitS : sameStand linksFull a a' = true
  /-- a test on the table and the meaning's list of extra public tests -/
  hTab : digTableB Mg.more linksFull PS k a l (shift sub) = true
  /-- a test on the numbers -/
  hbf : bookFit N PS told = true
  hn : told[k]? = some []
  /-- on the numbers and the piece: every sampled tenant that is open in front lies below -/
  hbaseS : ∀ e ∈ sampledIn N ((openSets linksFull PS (start linksFull))[k]?.getD []),
    e.1 < q.base
  /-- where the piece accepts -/
  fObj : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    a.1.failed = none → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace SET true x) b.1 = true →
    DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) (k + 1) b →
    ∀ w, Mg.forms l (7 + shift sub) "objects" (z, b.1) (strsOf Fr b.2) w →
    ∀ g F', (Desc.K3.seatDigits claim).fork b.1 = some F' →
    (Desc.K3.seatDigits claim).heard b.1 = some g →
    K3OutRows tl.f9 5 x.F.next
      (digNu x tl Dn L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F'
  othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a) ++
      pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
        (Desc.First.rowOf linksFull a)),
    k3Like r = false → Mg.pub r (z, v.1) = true
  othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a),
    (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → Mg.pubP r (z, v.1)
  rides : RidesAtR N Mg Rch k q b'
  /-- test on the list of rounds: three of `DigSits` -/
  some : ∀ i, ∃ y ∈ ms, Alike y ⟨digSending x Dn L.rad (fun j => L.seat x.link true j.1), i⟩
  sent : ∀ i : Fin (digList x Dn L.rad).length,
    ∃ t ∈ [2, 0, 1], L.seat x.link true i.1 ∈ N.sent l t
  fits : Desc.Sound.SeatFits G Dn.codes (digList x Dn L.rad) fun j => L.seat x.link true j.1

variable {G X Dn L N Mg Rch claim ms}

/-- The like at the digits. -/
theorem digRest_of_owed {seats : List (ℕ × ℕ)} (fold : K3Fold Rch Dn) {l : ℕ} (hl : l < 25)
    {sub : ModelPart} {x : Desc.First.Look.Place} {tl : HTailF2} (hx : digAt X l = some (x, tl))
    {q : PieceT} {b' : Desc.Block Desc.First.S Cl} {told : List (List Desc.Oracle)}
    (W : DigOwedR G X Dn L N Mg Rch claim ms (IM.k3Place l true) (MgAt.nextOf l true) (k3K l true)
      l sub x tl (smpDigits seats Dn L.rad L.seat x) q b' told) :
    DigRestR G X Dn L N Mg Rch claim (smpNamed Dn.codes seats) ms (IM.k3Place l true)
      (MgAt.nextOf l true) (k3K l true) l sub x tl (smpDigits seats Dn L.rad L.seat x) q b'
      told := by
  have hlook : lookAt X l true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  exact
  { hfit := W.hfit
    hOp := W.hOp
    hfitS := W.hfitS
    hTab := W.hTab
    hbf := W.hbf
    hn := W.hn
    hbaseS := W.hbaseS
    fObj := W.fObj
    othersPub := W.othersPub
    othersP := W.othersP
    rides := W.rides
    hk1 := MgAt.next_place hl true
    sits := ⟨W.some, smpNamed_bySeat _ _, W.sent, W.fits,
      fun z s i => smpDigits_is seats Dn L.rad L.seat x z s i⟩
    ownIn := fun z u _ hr hu => by
      rw [IM.lookAt_link hlook]
      exact fold.ownIs l hl true ((z, u.1), u.2) hr hu }

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (codes : Codes) (shape : Params.ReqShape)
  (pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl
    (Desc.Wit (CellsQ rows cols) Tok MsgT)))
  (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V)
  (told : List (List Desc.Oracle)) (arrs : Array (Nat × String))

/-- **THE LEDGER, EACH DEBT ONCE.** -/
structure K3OwedR : Prop where
  /-- on 𝔇 and Mg alone -/
  hM : Mg.more = {}
  es : 𝔇.smp = smpNamed 𝔇.cs seats
  hD : 𝔇.digitsPart = digitsPartK3 X 𝔇.sent 𝔇.l3
  hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → 𝔇.decT c y' = 𝔇.decT c y
  hIn : InOrderReads Mg
  /-- what the kind's paid fields spend of the facts along the fold -/
  fold : K3Fold Rch 𝔇.sent
  dig : ∀ l < 25, ∀ sub, linksFull[l]? = some sub → ∀ x tl, digAt X l = some (x, tl) →
    ∀ q, pieces[k3K l true]? = some q → ∀ b', k3Const X codes shape l true = some b' →
      DigOwedR 𝔇.G X 𝔇.sent 𝔇.l3 𝔇.N (mgAll 𝔇 Mg) Rch K3Lot.ofForm 𝔇.ms (IM.k3Place l true)
        (MgAt.nextOf l true) (k3K l true) l sub x tl
        (smpDigits seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  att : ∀ l < 25, ∀ x A tl, attAt X l = some (x, A, tl) →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      lookAt X l false = some x ∧
      AttOwedR 𝔇 Mg Rch K3Lot.ofForm num (idx l) tls tok (IM.k3Place l false)
        (MgAt.nextOf l false)
        (k3K l false) l x A tl (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  lay : ∀ l < 25, ∀ x tl, layAt X l = some x → tlAt X l = some tl →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      lookAt X l false = some x ∧
      LayOwedR 𝔇 Mg Rch K3Lot.ofForm num (idx l) tls tok (IM.k3Place l false)
        (MgAt.nextOf l false)
        (k3K l false) l x tl (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  head : ∀ x, Desc.Kinds.Head.Law.headAt X = some x →
    ∀ q, pieces[k3K 24 false]? = some q → ∀ b', k3Const X codes shape 24 false = some b' →
      HeadRestR 𝔇 Mg Rch K3Lot.ofForm seats s₀ x q b' arrs (IM.k3Place 24 false)
        (MgAt.nextOf 24 false) told

variable {𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok told arrs}

/-- **It gives the ledger with its double entries.** -/
theorem k3Rest_of_owed
    (W : K3OwedR 𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok told arrs) :
    K3RestR 𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok MgAt.nextOf told arrs where
  hM := W.hM
  hS := fun c z s s' => W.hd c (z, s') (z, s) rfl
  es := W.es
  hD := W.hD
  hd := W.hd
  hIn := W.hIn
  fold := W.fold
  dig := fun l hl sub hsub x tl hx q hq b' hb =>
    W.es ▸ digRest_of_owed W.fold hl hx (W.dig l hl sub hsub x tl hx q hq b' hb)
  att := fun l hl x A tl hx q hq b' hb =>
    ⟨(W.att l hl x A tl hx q hq b' hb).1,
      attRest_of_owed W.hM W.es W.hd W.hIn W.fold hl (W.att l hl x A tl hx q hq b' hb).1
        (W.att l hl x A tl hx q hq b' hb).2⟩
  lay := fun l hl x tl hx ht q hq b' hb =>
    ⟨(W.lay l hl x tl hx ht q hq b' hb).1,
      layRest_of_owed W.hM W.es W.hd W.hIn W.fold hl (W.lay l hl x tl hx ht q hq b' hb).1
        (W.lay l hl x tl hx ht q hq b' hb).2⟩
  head := W.head

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attRest_of_owed
#print axioms VerifiableInference.OnPublicFiles.layRest_of_owed
#print axioms VerifiableInference.OnPublicFiles.digRest_of_owed
#print axioms VerifiableInference.OnPublicFiles.k3Rest_of_owed
