-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsMean.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING mgAll
(Johnson/Desc/Sound/MgAll.lean): AttMeanR AND LayMeanR (Johnson/Desc/First/Look/K3CallsMeanR.lean)
AT Mg := mgAll Dm Mg, D := Dm.sent, L := Dm.l3, N := Dm.N: what the kind's law in the second form of
the chain of promises asks of the meaning at an attention and at a layers' link. BY CALLS ALONE:
attMean_ofR, layMean_ofR at attTiesR_mgAll, layTiesR_mgAll, behindPartsR_mgAll (MgAt/K3Calls.lean);
"an accept of the seated piece leaves all but the open link's ledger and what the lookup's verifier
has heard" is paid here (seat_yes, k3_calls_sameBut). It proves nothing new of any sub-protocol. NO
SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' meaning at the kind's items.
Used by K3CallsRestR.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: those of MgAt/K3Calls.lean; readers, codes, shape, a, b': those of Desc.K3.theStated.

WHAT IS LEFT, EACH A NAMED PREMISE, BOOKED BY SORT:
  THE VALUE IS LAID: h, hOk. THE PIECE: hback.
  TESTS ON THE PUBLIC PARAMETERS AND THE LIST OF ROUNDS: hla, hpcX, hpc, hsub, hlook, hx | hna, ht,
    hq, hg, hl, hhd · cellsIn, HA | HL, hT, hU (theorems in the goals' scope) · T, O1, Own, hgs,
    fit,
    LS · hseat, hpin, hsent, hbase, hns · here, next, stand, bfit, tells, hfit, askFresh.
  A FACT ALONG THE FOLD: ownIn (OwnIs).
  TERMS OF mgAll's PARAMETERS: hread (the row's reader of OOD samples reads the statement and
    the book) · hsmpT · hS · hhid, hb · reads · hIn.
  LEFT HERE: objects · rides. THE RULE OF FOOTPRINTS (PubFoot.lean): bPub, bPubP.

Main names: `attMeanR_mgAll`, `layMeanR_mgAll`.

Limits. A rule over letters. The full size's written list of segments (linksFull).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3Calls

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
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT)) (claim : Aff → Cl)
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes) (shape : Params.ReqShape)
  {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V) {g k l : ℕ}
  {x : Desc.First.Look.Place} {a a' : Desc.Place} {b' : Desc.Block Desc.First.S Cl}
  {told : List (List Desc.Oracle)}
  {smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
    Option ((attSg x Dm.sent Dm.rad3).om i).Smp}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  {Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **AttMeanR at the composed meaning.** -/
theorem attMeanR_mgAll
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hla : a.link = some l) (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hsub : linksFull[l]? = some .attention) (hlook : lookAt X l false = some x)
    (hback : q.back = [])
    (hread : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → smp s' = smp s)
    (hseat : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
      (Dm.seat3 x.link false i.1).1 < q.base)
    (hpin : Item.pin l 0 ∈ (openSets linksFull PS (start linksFull))[k]?.getD [])
    (hsent : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
      Dm.seat3 x.link false i.1 ∈ Dm.N.sent l 0)
    (hg : g < 12) (hl : l = 2 * g + 1) (hhd : l ≠ headLink X)
    (T : linkTieB X Dm.sent Dm.rad3 num idx x.link (tls x.link) = true)
    (O1 : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id)
    (Own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N) (hgs : GroupsSeated Dm.ms Dm.N)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (LS : ListSits Dm.G x Dm.sent Dm.rad3 seatL Dm.smp smp Dm.ms Dm.N l)
    (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns)
    (here : PS[k]? = some a) (next : PS[k + 1]? = some a')
    (stand : sameStand linksFull a a' = true) (bfit : bookFit Dm.N PS told = true)
    (tells : told[k]? = some []) (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (askFresh : Pub.linkFresh l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
    (hbase : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
      t.1 < q.base)
    (hIn : InOrderReads Mg)
    (hsmpT : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → Dm.smp (z, s') = Dm.smp (z, s))
    (hS : ∀ c z s s', Dm.decT c (z, s) = Dm.decT c (z, s'))
    (hhid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (hb : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j)
    (reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (ownIn : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → OwnIs Dm.sent x.link u.1)
    (hx : attAt X l = some (x, Road.Hd.shapeA X g, tls x.link))
    (cellsIn : planesInB x (Road.Hd.shapeA X g) (tls x.link) = true)
    (HA : AttOK SET x (Road.Hd.shapeA X g) (tls x.link) Dm.sent Dm.rad3)
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c)
    (objects : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x (Road.Hd.shapeA X g) (tls x.link) Dm.sent Dm.rad3 seatL Dm.arr
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w)
    (bPub : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true)
    (bPubP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a),
        p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1))
    (rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b') :
    AttMeanR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) claim Rch a k l x (Road.Hd.shapeA X g)
      (tls x.link) smp q b' := by
  have e : placeAt X l false = some theP := by
    unfold placeAt
    rw [hlook]
    rfl
  have hp2 : Desc.K3.pieceAt X l false = 2 := hpcX.symm.trans hpc
  have hSB : ∀ B', SeatOf b' B' → ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v →
      SameBut u.1 v.1 := by
    intro B' hB u τ v hout
    obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
      seat_yes claim readers codes shape h hOk hla hpcX e hback B' hB u v ⟨τ, hout⟩
    exact k3_calls_sameBut claim piece laid before _ guests _ _ rs cols hd
  have hb0 : ∀ t ∈ Dm.N.sent l 0, t.1 < q.base := fun t ht =>
    hbase t (List.mem_flatMap.2 ⟨_, hpin, ht⟩)
  have Bp : ∀ B', SeatOf b' B' → ∀ z : P,
      BehindPartsR (Fr := Fr) x SET Dm.N (mgAll Dm Mg) linksFull PS z k l 2
        (Dm.sent.arrayOf.getD l #[]) a a' told
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
        (fun u => Rch k ((z, u.1), u.2)) := fun B' hB z =>
    behindPartsR_mgAll (sub := .attention) Dm Mg B' z hIn hns hlook hp2 here next hla hsub hpc stand
      bfit tells hfit askFresh hbase (hSB B' hB) hsmpT (bPub B' hB z) (bPubP B' hB z)
  exact attMean_ofR (L := Dm.l3) Dm.G claim readers codes shape h hOk hla hpcX hpc hsub e hback HA
    hread hseat hpin hsent Bp
    (fun B' hB z => attTiesR_mgAll Dm Mg claim tls tok B' z hlook hp2 hg hl hhd T O1 Own hgs fit LS
      hb0 (hSB B' hB) hsmpT hS hhid hb reads (ownIn z) hx cellsIn HA hT hU (objects B' hB z))
    rides

/-- **LayMeanR at the composed meaning**: the committed table's letters are the terms of
Johnson/Desc/First/Look/K3StoredThree.lean; s₀: any state. -/
theorem layMeanR_mgAll (s₀ : Desc.First.S)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hla : a.link = some l) (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hsub : linksFull[l]? = some .layers) (hlook : lookAt X l false = some x)
    (hback : q.back = [])
    (hread : ∀ s s' : Desc.First.S, s'.st = s.st → s'.book = s.book → smp s' = smp s)
    (hseat : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
      (Dm.seat3 x.link false i.1).1 < q.base)
    (hpin : Item.pin l 0 ∈ (openSets linksFull PS (start linksFull))[k]?.getD [])
    (hsent : ∀ i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length,
      Dm.seat3 x.link false i.1 ∈ Dm.N.sent l 0)
    (hg : g < 12) (hl : l = 2 * g) (hhd : l ≠ headLink X)
    (T : linkTieB X Dm.sent Dm.rad3 num idx x.link (tls x.link) = true)
    (O1 : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id)
    (Own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N) (hgs : GroupsSeated Dm.ms Dm.N)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (LS : ListSits Dm.G x Dm.sent Dm.rad3 seatL Dm.smp smp Dm.ms Dm.N l)
    (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns)
    (here : PS[k]? = some a) (next : PS[k + 1]? = some a')
    (stand : sameStand linksFull a a' = true) (bfit : bookFit Dm.N PS told = true)
    (tells : told[k]? = some []) (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (askFresh : Pub.linkFresh l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
    (hbase : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
      t.1 < q.base)
    (hIn : InOrderReads Mg)
    (hsmpT : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → Dm.smp (z, s') = Dm.smp (z, s))
    (hS : ∀ c z s s', Dm.decT c (z, s) = Dm.decT c (z, s'))
    (hhid : ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (hb : ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j)
    (reads : ∀ w : Desc.Wit (CellsQ rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w))
    (ownIn : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → OwnIs Dm.sent x.link u.1)
    (hna : attAt X l = none) (hx : layAt X l = some x) (ht : tlAt X l = some (tls x.link))
    (hq : l / Desc.First.Look.stepOf X = g) (HL : LayOK SET x)
    (objects : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x (pubAt X (l / Desc.First.Look.stepOf X)) (tls x.link) Dm.sent Dm.rad3
        (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard v.1 w)
    (bPub : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true)
    (bPubP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a),
        p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1))
    (rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b') :
    LayMeanR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) claim Rch a k l x (tls x.link) smp smpWc
      (strWc Dm.decT s₀) q b' := by
  have e : placeAt X l false = some theP := by
    unfold placeAt
    rw [hlook]
    rfl
  have hp2 : Desc.K3.pieceAt X l false = 2 := hpcX.symm.trans hpc
  have hSB : ∀ B', SeatOf b' B' → ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v →
      SameBut u.1 v.1 := by
    intro B' hB u τ v hout
    obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
      seat_yes claim readers codes shape h hOk hla hpcX e hback B' hB u v ⟨τ, hout⟩
    exact k3_calls_sameBut claim piece laid before _ guests _ _ rs cols hd
  have hb0 : ∀ t ∈ Dm.N.sent l 0, t.1 < q.base := fun t ht =>
    hbase t (List.mem_flatMap.2 ⟨_, hpin, ht⟩)
  have Bp : ∀ B', SeatOf b' B' → ∀ z : P,
      BehindPartsR (Fr := Fr) x SET Dm.N (mgAll Dm Mg) linksFull PS z k l 2
        (Dm.sent.arrayOf.getD l #[]) a a' told
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
        (fun u => Rch k ((z, u.1), u.2)) := fun B' hB z =>
    behindPartsR_mgAll (sub := .layers) Dm Mg B' z hIn hns hlook hp2 here next hla hsub hpc stand
      bfit tells hfit askFresh hbase (hSB B' hB) hsmpT (bPub B' hB z) (bPubP B' hB z)
  exact layMean_ofR (L := Dm.l3) Dm.G claim readers codes shape h hOk hla hpcX hpc hsub e hback HL
    hread (fun _ _ _ _ => rfl)
    (fun z y τ => Stored.hstrW_c (ckP .two) s₀ z q.base q.ds y τ) hseat
    ⟨((), fun s => s.elim)⟩ hpin hsent Bp
    (fun B' hB z => layTiesR_mgAll Dm Mg claim tls tok B' z s₀ hlook hp2 hg hl hhd T O1 Own hgs fit
      LS hb0 (hSB B' hB) hsmpT hS hhid hb reads (ownIn z) hna hx ht hq HL (objects B' hB z))
    rides

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attMeanR_mgAll
#print axioms VerifiableInference.OnPublicFiles.layMeanR_mgAll
