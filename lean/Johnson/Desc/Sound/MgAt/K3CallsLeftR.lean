-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsLeftR.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll: AttRestR AND LayRestR (Johnson/Desc/Sound/MgAt/K3CallsRestR.lean) WITH EVERY FIELD THAT IS A
THEOREM IN THE GOALS' SCOPE LAID IN: one smaller structure for both sorts of link, CallsLeftR, and
two builders, attRestR_scope, layRestR_scope, at tls := Meaning.tlAt X. LAID IN: at attention: odd,
shapeIs, cellsIn, tabs, room; at the layers: even, noAtt, step; at both: hlt, hhd, htl, fit. The
sentence on the objects, which parts by the sort, is the letter Obj. A carrying of theorems in
scope: nothing new is shown. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' meaning at the kind's items.
Used by K3CallsOwedScope.lean (Johnson/Desc/Sound/MgAt/): attAt_even alone. CallsLeftR and the two
  builders have no caller.
LETTERS: those of MgAt/K3CallsRestR.lean; Z, pp, lay as in the scope's theorems; g: a group below
12;
  Obj: what the row's opened item "objects" must say of the state behind and the witness.

EACH FIELD's DOCSTRING OPENS WITH ITS BOOKING, as in AttRestR: test · fold fact ‹field› · term ·
accept.

Main names: `CallsLeftR` · `attAt_even` · `attRestR_scope`, `layRestR_scope`.

Limits. The full size's scope alone. The links below 24.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsRestR
import Johnson.Desc.First.Look.K3CallsModelSeats
import Johnson.Desc.First.Look.K3PlanLetters
import Johnson.Desc.First.Look.K3TabsScope
import Johnson.Goal.Meaning.ScopeCore

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

/-- At a link with an even number attention's reader answers nothing. -/
theorem attAt_even {X : Verify.Public} {i : ℕ} (h : i % 2 = 0) : attAt X i = none := by
  unfold attAt
  rw [if_neg (fun h' => by have := h'.2; omega)]

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

/-- **WHAT IS LEFT AT ONE LINK's CALLS, IN THE GOALS' SCOPE**: both sorts. -/
structure CallsLeftR
    (smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
      Option ((attSg x Dm.sent Dm.rad3).om i).Smp)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle))
    (Obj : Desc.First.S → Desc.Wit (CellsQ rows cols) Tok MsgT → Prop) : Prop where
  /-- test on the public parameters and the layout -/
  tie : linkTieB X Dm.sent Dm.rad3 num idx x.link (tls x.link) = true
  /-- test on the list of rounds: a member's number is its label's; no pad's place -/
  one : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id
  /-- test on the table's numbers: one tenant with that number; no pad's place -/
  own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N
  /-- test on the table's numbers -/
  seated : GroupsSeated Dm.ms Dm.N
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
  /-- term: reader's and owner's readings agree at every witness (WordsAtQ.lean: readsOne_readAt) -/
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
    Obj v.1 w
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

variable {Dm Mg Rch num idx tok a a' k x}
  {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {g : ℕ} {tl : HTailF2}
  {smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
    Option ((attSg x Dm.sent Dm.rad3).om i).Smp}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  {b' : Desc.Block Desc.First.S Cl} {told : List (List Desc.Oracle)}

/-- **AttRestR, in scope.** -/
theorem attRestR_scope {A : Attention.Shape} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : Verify.publicOf Z.pol Z.KL lay = .ok X) (hg : g < 12)
    (hx : attAt X (2 * g + 1) = some (x, A, tl))
    (R : CallsLeftR Dm Mg Rch num idx (_root_.Meaning.tlAt X) tok a a' k (2 * g + 1) x smp q b' told
      (attObjects x A tl Dm.sent Dm.rad3 seatL Dm.arr (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard)) :
    AttRestR Dm Mg Rch claim num idx (_root_.Meaning.tlAt X) tok a a' k (2 * g + 1) x A tl smp q b'
      told := by
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR h
  obtain ⟨-, hA, htl, hlook⟩ := attAt_letters hZ hR h hg hx
  obtain ⟨x', a0, hlook', -, e', -, hc⟩ := attAt_scope hZ hR h (l := 2 * g + 1) (by omega)
    (by omega) Dm.sent Dm.rad3
  have ex : x' = x := Option.some.inj (hlook'.symm.trans hlook)
  subst ex
  have e1 := Option.some.inj (e'.symm.trans hx)
  have eA : a0.S = A := congrArg (fun t => t.2.1) e1
  have et : a0.seam.tl = tl := congrArg (fun t => t.2.2) e1
  rw [eA, et] at hc
  obtain ⟨hT, hU⟩ := tabsAre_scope hZ hR h hg hlook
  have hk : (2 * g + 1) / 2 = g := by omega
  exact
  { odd := by omega
    shapeIs := by rw [hk]; exact hA
    cellsIn := hc
    tabs := by rw [hA]; exact hT
    room := by rw [hA]; exact hU
    hlt := by omega
    hhd := by
      unfold headLink
      rw [if_pos hp4, hN]
      omega
    htl := htl
    fit := fit_at_tlAt h (Road.Hd.core_of_scope hZ hR h)
    tie := by rw [htl]; exact R.tie
    one := R.one
    own := R.own
    seated := R.seated
    sits := R.sits
    pin := R.pin
    base := R.base
    slots := R.slots
    next := R.next
    stand := R.stand
    book := R.book
    tells := R.tells
    pubs := R.pubs
    fresh := R.fresh
    order := R.order
    smpSt := R.smpSt
    noState := R.noState
    hid := R.hid
    small := R.small
    reads := R.reads
    ownIn := R.ownIn
    objects := R.objects
    othersPub := R.othersPub
    othersP := R.othersP
    rides := R.rides }

/-- **LayRestR, in scope.** -/
theorem layRestR_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : Verify.publicOf Z.pol Z.KL lay = .ok X) (hg : g < 12)
    (hlook : lookAt X (2 * g) false = some x) (ht : tlAt X (2 * g) = some tl)
    (R : CallsLeftR Dm Mg Rch num idx (_root_.Meaning.tlAt X) tok a a' k (2 * g) x smp q b' told
      (layObjects x (pubAt X (2 * g / Desc.First.Look.stepOf X)) tl Dm.sent Dm.rad3
        (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard)) :
    LayRestR Dm Mg Rch claim num idx (_root_.Meaning.tlAt X) tok a a' k (2 * g) x tl smp q b'
      told := by
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR h
  have htl : tl = _root_.Meaning.tlAt X x.link := by
    rw [lookAt_link hlook]
    exact lay_letters hZ hR h hg ht
  exact
  { even := by omega
    noAtt := attAt_even (by omega)
    step := by
      unfold Desc.First.Look.stepOf
      rw [if_pos hp4]
    hlt := by omega
    hhd := by
      unfold headLink
      rw [if_pos hp4, hN]
      omega
    htl := htl
    fit := fit_at_tlAt h (Road.Hd.core_of_scope hZ hR h)
    tie := by rw [htl]; exact R.tie
    one := R.one
    own := R.own
    seated := R.seated
    sits := R.sits
    pin := R.pin
    base := R.base
    slots := R.slots
    next := R.next
    stand := R.stand
    book := R.book
    tells := R.tells
    pubs := R.pubs
    fresh := R.fresh
    order := R.order
    smpSt := R.smpSt
    noState := R.noState
    hid := R.hid
    small := R.small
    reads := R.reads
    ownIn := R.ownIn
    objects := R.objects
    othersPub := R.othersPub
    othersP := R.othersP
    rides := R.rides }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attRestR_scope
#print axioms VerifiableInference.OnPublicFiles.layRestR_scope
