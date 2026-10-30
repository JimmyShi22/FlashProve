-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsRestR.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll: WHAT IS LEFT AT ONE PLACE, AS ONE STRUCTURE: AttRestR, LayRestR: the premises of
attMeanR_mgAll, layMeanR_mgAll (Johnson/Desc/Sound/MgAt/K3CallsMean.lean) that are neither facts on
the constant, the piece and the place, nor what the kind's structure of public tests hands (attAt,
layAt, tlAt, AttOK, LayOK), nor paid at every value of mgAll's parameters. After the digits'
DigRestR (Johnson/Desc/First/Look/K3DigitsRestR.lean). attMeanR_of_rest, layMeanR_of_rest call the
two theorems, which stay as they are. A bundling: nothing new is shown. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' meaning at the kind's items.
Used by K3CallsLeftR.lean, K3Mean.lean, K3Owed.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: those of MgAt/K3CallsMean.lean. The group is l / 2. A, tl: what attAt (layAt, tlAt)
answers:
  the fields shapeIs and htl tie them to Hd.shapeA X (l / 2) and tls x.link. z₀: any value of the
  public part.

EACH FIELD's DOCSTRING OPENS WITH ITS BOOKING: test · fold fact ‹field› · term · accept.
FEWER THAN THE TWO THEOREMS' PREMISES: hseat and hsent come from sits.sent, pin and base; hread from
  sits.smpIs and smpSt; hg and hl from the parity and hlt.

Main names: `AttRestR`, `attMeanR_of_rest` · `LayRestR`, `layMeanR_of_rest`.

Limits. A rule over letters. The full size's written list of segments (linksFull).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsMean

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

/-- **WHAT IS LEFT AT ONE ATTENTION LINK's CALLS.** -/
structure AttRestR (A : Attention.Shape) (tl : HTailF2)
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
  /-- test on the list of rounds (some, sent, fits) and term: the two readers of OOD samples
  (bySeat, smpIs) -/
  sits : ListSits Dm.G x Dm.sent Dm.rad3 seatL Dm.smp smp Dm.ms Dm.N l
  /-- test on the table: the pin of moment 0 is open in front -/
  pin : Item.pin l 0 ∈ (openSets linksFull PS (start linksFull))[k]?.getD []
  /-- test on the numbers and the piece: every sampled tenant that is open in front lies below -/
  base : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
    t.1 < q.base
  /-- test: the built segment's number of slots is the place's -/
  slots : (Dm.built[l]?).map (·.ns) = some (theP).ns
  /-- test on the table: the next place -/
  next : PS[k + 1]? = some a'
  /-- test on the table -/
  stand : sameStand linksFull a a' = true
  /-- test on the numbers -/
  book : bookFit Dm.N PS told = true
  /-- test on the numbers: this sub-protocol tells no tree -/
  tells : told[k]? = some []
  /-- test on the table and the meaning's list of extra public tests -/
  pubs : pubFit (mgAll Dm Mg).more linksFull PS = true
  /-- test on the table and that list -/
  fresh : Pub.linkFresh l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD []
  /-- term: "in order" of the meaning beneath reads the statement, the check and the request -/
  order : InOrderReads Mg
  /-- term: the reader of OOD samples reads the statement alone -/
  smpSt : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → Dm.smp (z, s') = Dm.smp (z, s)
  /-- term: the committed table's decoder does not read the state -/
  noState : ∀ c z s s', Dm.decT c (z, s) = Dm.decT c (z, s')
  /-- term: H reads a witness as hidAtSeat does (there: rfl, with seatsOf_all) -/
  hid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- term: the like for the part "small" -/
  small : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j
  /-- term: reader's and owner's readings agree at every witness (readsOne_readAt, Johnson/P5J/) -/
  reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- fold fact ownIs, at the border k -/
  ownIn : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → OwnIs Dm.sent x.link u.1
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

/-- **WHAT IS LEFT AT ONE LAYERS' LINK's CALLS.** -/
structure LayRestR (tl : HTailF2)
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
  /-- test on the list of rounds (some, sent, fits) and term: the two readers of OOD samples
  (bySeat, smpIs) -/
  sits : ListSits Dm.G x Dm.sent Dm.rad3 seatL Dm.smp smp Dm.ms Dm.N l
  /-- test on the table: the pin of moment 0 is open in front -/
  pin : Item.pin l 0 ∈ (openSets linksFull PS (start linksFull))[k]?.getD []
  /-- test on the numbers and the piece: every sampled tenant that is open in front lies below -/
  base : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
    t.1 < q.base
  /-- test: the built segment's number of slots is the place's -/
  slots : (Dm.built[l]?).map (·.ns) = some (theP).ns
  /-- test on the table: the next place -/
  next : PS[k + 1]? = some a'
  /-- test on the table -/
  stand : sameStand linksFull a a' = true
  /-- test on the numbers -/
  book : bookFit Dm.N PS told = true
  /-- test on the numbers: this sub-protocol tells no tree -/
  tells : told[k]? = some []
  /-- test on the table and the meaning's list of extra public tests -/
  pubs : pubFit (mgAll Dm Mg).more linksFull PS = true
  /-- test on the table and that list -/
  fresh : Pub.linkFresh l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD []
  /-- term: "in order" of the meaning beneath reads the statement, the check and the request -/
  order : InOrderReads Mg
  /-- term: the reader of OOD samples reads the statement alone -/
  smpSt : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → Dm.smp (z, s') = Dm.smp (z, s)
  /-- term: the committed table's decoder does not read the state -/
  noState : ∀ c z s s', Dm.decT c (z, s) = Dm.decT c (z, s')
  /-- term: H reads a witness as hidAtSeat does (there: rfl, with seatsOf_all) -/
  hid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- term: the like for the part "small" -/
  small : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j
  /-- term: reader's and owner's readings agree at every witness (readsOne_readAt, Johnson/P5J/) -/
  reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
    (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
    (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w)
  /-- fold fact ownIs, at the border k -/
  ownIn : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → OwnIs Dm.sent x.link u.1
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

variable {Dm Mg Rch claim num idx tls tok a a' k l x}
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes) (shape : Params.ReqShape)
  {tl : HTailF2}
  {smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
    Option ((attSg x Dm.sent Dm.rad3).om i).Smp}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  {b' : Desc.Block Desc.First.S Cl} {told : List (List Desc.Oracle)}

/-- **AttMeanR FROM WHAT IS LEFT.** -/
theorem attMeanR_of_rest {A : Attention.Shape} (z₀ : P)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hsub : linksFull[l]? = some .attention) (here : PS[k]? = some a)
    (hlook : lookAt X l false = some x)
    (hx : attAt X l = some (x, A, tl)) (HA : AttOK SET x A tl Dm.sent Dm.rad3)
    (R : AttRestR Dm Mg Rch claim num idx tls tok a a' k l x A tl smp q b' told) :
    AttMeanR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) claim Rch a k l x A tl smp q b' := by
  have hread : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → smp s' = smp s := by
    intro s s' hst _
    funext i
    rw [R.sits.smpIs z₀ s' i, R.sits.smpIs z₀ s i, R.smpSt z₀ s s' hst]
  have hb0 : ∀ t ∈ Dm.N.sent l 0, t.1 < q.base := fun t ht =>
    R.base t (List.mem_flatMap.2 ⟨_, R.pin, ht⟩)
  have hA := R.shapeIs
  have htl := R.htl
  subst hA
  subst htl
  exact attMeanR_mgAll (g := l / 2) Dm Mg claim readers codes shape tls tok h hOk hla hpcX hpc hsub
    hlook hback hread (fun i => hb0 _ (R.sits.sent i)) R.pin R.sits.sent
    (by have := R.hlt; omega) (by have := R.odd; omega) R.hhd R.tie R.one R.own R.seated R.fit
    R.sits R.slots here R.next R.stand R.book R.tells R.pubs R.fresh R.base R.order R.smpSt
    R.noState R.hid R.small R.reads R.ownIn hx R.cellsIn HA R.tabs R.room R.objects R.othersPub
    R.othersP R.rides

/-- **LayMeanR FROM WHAT IS LEFT.** s₀: any state. -/
theorem layMeanR_of_rest (z₀ : P) (s₀ : Desc.First.S)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hsub : linksFull[l]? = some .layers) (here : PS[k]? = some a)
    (hlook : lookAt X l false = some x)
    (hx : layAt X l = some x) (ht : tlAt X l = some tl) (HL : LayOK SET x)
    (R : LayRestR Dm Mg Rch claim num idx tls tok a a' k l x tl smp q b' told) :
    LayMeanR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) claim Rch a k l x tl smp smpWc
      (strWc Dm.decT s₀) q b' := by
  have hread : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → smp s' = smp s := by
    intro s s' hst _
    funext i
    rw [R.sits.smpIs z₀ s' i, R.sits.smpIs z₀ s i, R.smpSt z₀ s s' hst]
  have hb0 : ∀ t ∈ Dm.N.sent l 0, t.1 < q.base := fun t ht =>
    R.base t (List.mem_flatMap.2 ⟨_, R.pin, ht⟩)
  have htl := R.htl
  subst htl
  exact layMeanR_mgAll (g := l / 2) Dm Mg claim readers codes shape tls tok s₀ h hOk hla hpcX hpc
    hsub hlook hback hread (fun i => hb0 _ (R.sits.sent i)) R.pin R.sits.sent
    (by have := R.hlt; omega) (by have := R.even; omega) R.hhd R.tie R.one R.own R.seated R.fit
    R.sits R.slots here R.next R.stand R.book R.tells R.pubs R.fresh R.base R.order R.smpSt
    R.noState R.hid R.small R.reads R.ownIn R.noAtt hx ht R.step HL R.objects R.othersPub
    R.othersP R.rides

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attMeanR_of_rest
#print axioms VerifiableInference.OnPublicFiles.layMeanR_of_rest
