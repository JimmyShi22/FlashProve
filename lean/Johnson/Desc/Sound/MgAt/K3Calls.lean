-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3Calls.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING mgAll
(Johnson/Desc/Sound/MgAll.lean): the ties of the filling AttTiesR, LayTiesR
(Johnson/Desc/First/Look/K3CallsMeanR.lean) and the parts of the promise behind BehindPartsR
(Johnson/Desc/First/Look/K3CallsBehindR.lean) AT Mg := mgAll Dm Mg, D := Dm.sent, L := Dm.l3, N :=
Dm.N. BY CALLS ALONE: attTies_ofR, layTies_ofR, behindParts_ofR (K3CallsAtR.lean) at k3At_mgAll
(MgAt/K3At.lean) and MgAll.lean's own equations (mgAll_pin, mgAll_noColl, mgAll_shown, mgAll_pub
with pubAll_ledger, pubAll_freeAbove); "model" by att_model_at, lay_model_at (K3CallsModelFits.lean)
at mgAll_constr, mgAll_pinW and oneDec's decoder; "smallBack" by small_back (K3CallsSmallBack.lean);
"decodes" by decodes_at_seat (Johnson/Desc/Sound/DecodesAtPiece.lean); the committed table's three
by the kind's conduit (Johnson/Desc/First/Look/K3StoredThree.lean). It proves nothing of any
sub-protocol. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' meaning at the kind's items.
USER: Johnson/Desc/Sound/MgAt/K3CallsMean.lean (all three, beneath attMean_ofR, layMean_ofR) ·
  Johnson/Desc/Sound/MgAt/K3HeadBehindAt.lean (behindPartsR_mgAll).
LETTERS: Dm, Mg: mgAll's; num, idx, tls, tok: as in K3CallsModelFits.lean; Rch: a letter.

WHAT IS LEFT, EACH A NAMED PREMISE, BOOKED BY SORT:
  TESTS ON THE PUBLIC PARAMETERS AND THE LIST OF ROUNDS: hlook, hx, hp2, hg, hl, hhd · cellsIn, HA |
    HL, hT, hU (theorems in the goals' scope) · T (linkTieB) · O1 (OneNumber) · Own (OwnNamed) · hgs
    (GroupsSeated) · fit (sizesFit) · LS (ListSits) · hbase · in behindPartsR_mgAll: here, next, hs,
    hpc, stand, fit, tells, hfit, askFresh, hns, hbase.
  A FACT ALONG THE FOLD: ownIn (OwnIs).
  THE ACCEPT: hSB (an accept of the seated piece leaves all but the open link's ledger and what the
    lookup's verifier has heard: k3_calls_sameBut
    (Johnson/Desc/First/Look/K3CallsTurns.lean) gives it at what is seated).
  TERMS OF mgAll's PARAMETERS: hsmpT (the reader of OOD samples reads the statement alone) ·
    hS (the decoder does not read the state) · hhid, hb (H reads a witness as hidAtSeat does) ·
    reads (ReadsOne at every witness) · hIn (InOrderReads of the meaning beneath).
  LEFT HERE: objects. THE RULE OF FOOTPRINTS (Johnson/Desc/First/PubFoot.lean): bPub, bPubP.

Main names: `attTiesR_mgAll`, `layTiesR_mgAll`, `behindPartsR_mgAll`.

Limits. A rule over letters. The full size's written list of segments (linksFull).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.First.Look.K3CallsAtR
import Johnson.Desc.First.Look.K3CallsModelFits
import Johnson.Desc.First.Look.K3CallsSmallBack

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
  {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V) {g k l : ℕ}
  {x : Desc.First.Look.Place}
  {smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
    Option ((attSg x Dm.sent Dm.rad3).om i).Smp}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  (B' : Desc.Block Desc.First.S Cl) (z : P)
  {Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **AttTiesR at the composed meaning.** -/
theorem attTiesR_mgAll
    -- the public parameters and the list of rounds
    (hlook : lookAt X l false = some x) (hp2 : Desc.K3.pieceAt X l false = 2) (hg : g < 12)
    (hl : l = 2 * g + 1) (hhd : l ≠ headLink X)
    (T : linkTieB X Dm.sent Dm.rad3 num idx x.link (tls x.link) = true)
    (O1 : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id)
    (Own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N) (hgs : GroupsSeated Dm.ms Dm.N)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (LS : ListSits Dm.G x Dm.sent Dm.rad3 seatL Dm.smp smp Dm.ms Dm.N l)
    (hbase : ∀ t ∈ Dm.N.sent l 0, t.1 < q.base)
    -- the accept
    (hSB : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → SameBut u.1 v.1)
    -- terms of mgAll's parameters
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
    -- a fact along the fold
    (ownIn : ∀ u : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → OwnIs Dm.sent x.link u.1)
    (hx : attAt X l = some (x, Road.Hd.shapeA X g, tls x.link))
    (cellsIn : planesInB x (Road.Hd.shapeA X g) (tls x.link) = true)
    (HA : AttOK SET x (Road.Hd.shapeA X g) (tls x.link) Dm.sent Dm.rad3)
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c)
    -- left to other files
    (objects : ∀ u v : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x (Road.Hd.shapeA X g) (tls x.link) Dm.sent Dm.rad3 seatL Dm.arr
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w) :
    AttTiesR (Fr := Fr) Dm.G x (Road.Hd.shapeA X g) (tls x.link) Dm.sent Dm.rad3 SET seatL Dm.arr
      smp claim Dm.N (mgAll Dm Mg) linksFull PS z k l
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) :=
  attTies_ofR (L := Dm.l3) Dm.G claim B' z (k3At_mgAll Dm Mg) (mgAll_pin Dm Mg) (mgAll_noColl Dm Mg)
    hlook hx hp2 LS hbase
    (fun u τ v h e _ => congrFun (congrFun (hsmpT z u.1 v.1 (hSB u τ v h).st) e.1) e.2)
    cellsIn ownIn objects
    (att_model_at (H := oneDec Dm.decT Dm.H) tls tok seatL Dm.arr (mgAll_constr Dm Mg) hhid hb fit
      reads hg (lookAt_link hlook) hl hhd T O1 Own hgs HA hT hU z)
    (small_back (mgAll_constr Dm Mg) rfl hS hhd z (strictAt B' q))
    (fun u v ⟨τ, h⟩ _ hd =>
      decodes_at_seat Dm.decT (fun c a a' e => by
        obtain ⟨z1, s1⟩ := a
        obtain ⟨z2, s2⟩ := a'
        obtain rfl : z2 = z1 := e
        exact hS c z2 s2 s1) z (strictAt B' q) u v τ h hd)

/-- **LayTiesR at the composed meaning**: the committed table's letters are K3StoredThree.lean's
terms; s₀: any state (its reader of the string does not read it, by hS). -/
theorem layTiesR_mgAll (s₀ : Desc.First.S)
    -- the public parameters and the list of rounds
    (hlook : lookAt X l false = some x) (hp2 : Desc.K3.pieceAt X l false = 2) (hg : g < 12)
    (hl : l = 2 * g) (hhd : l ≠ headLink X)
    (T : linkTieB X Dm.sent Dm.rad3 num idx x.link (tls x.link) = true)
    (O1 : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id)
    (Own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N) (hgs : GroupsSeated Dm.ms Dm.N)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (LS : ListSits Dm.G x Dm.sent Dm.rad3 seatL Dm.smp smp Dm.ms Dm.N l)
    (hbase : ∀ t ∈ Dm.N.sent l 0, t.1 < q.base)
    -- the accept
    (hSB : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → SameBut u.1 v.1)
    -- terms of mgAll's parameters
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
    -- a fact along the fold
    (ownIn : ∀ u : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → OwnIs Dm.sent x.link u.1)
    (hna : attAt X l = none) (hx : layAt X l = some x) (ht : tlAt X l = some (tls x.link))
    (hq : l / Desc.First.Look.stepOf X = g) (HL : LayOK SET x)
    -- left to other files
    (objects : ∀ u v : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x (pubAt X (l / Desc.First.Look.stepOf X)) (tls x.link) Dm.sent Dm.rad3
        (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard v.1 w) :
    LayTiesR (Fr := Fr) Dm.G x (pubAt X (l / Desc.First.Look.stepOf X)) (tls x.link) Dm.sent Dm.rad3
      (oWc rows cols) wOfC rows cols SET seatL Dm.arr smp smpWc (strWc Dm.decT s₀ z) msgWc claim
      Dm.N (mgAll Dm Mg) linksFull PS z k l
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) :=
  layTies_ofR (L := Dm.l3) Dm.G claim B' z (k3At_mgAll Dm Mg) (mgAll_pin Dm Mg) (mgAll_noColl Dm Mg)
    hlook hna hx ht hp2 LS hbase
    (fun u τ v h e _ => congrFun (congrFun (hsmpT z u.1 v.1 (hSB u τ v h).st) e.1) e.2)
    (fun u h => Stored.tabIn_c s₀ z u h)
    (fun u w h => Stored.pinWIn_c hS s₀ z u w h)
    (fun u w h => Stored.pinWOut_c hS s₀ z u w h)
    ownIn objects
    (lay_model_at (H := oneDec Dm.decT Dm.H) tls tok seatL Dm.arr (mgAll_constr Dm Mg) hhid hb fit
      reads hg (lookAt_link hlook) hl hhd T O1 Own hgs hq HL (mgAll_pinW Dm Mg) rfl z)
    (small_back (mgAll_constr Dm Mg) rfl hS hhd z (strictAt B' q))
    (fun u v ⟨τ, h⟩ _ hd =>
      decodes_at_seat Dm.decT (fun c a a' e => by
        obtain ⟨z1, s1⟩ := a
        obtain ⟨z2, s2⟩ := a'
        obtain rfl : z2 = z1 := e
        exact hS c z2 s2 s1) z (strictAt B' q) u v τ h hd)

/-- **BehindPartsR at the composed meaning**, at every sort of segment. -/
theorem behindPartsR_mgAll {sub : ModelPart} {a a' : Desc.Place} {told : List (List Desc.Oracle)}
    (hIn : InOrderReads Mg)
    (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns)
    (hlook : lookAt X l false = some x)
    (hpX : Desc.K3.pieceAt X l false = 2 + shift sub)
    (here : PS[k]? = some a) (next : PS[k + 1]? = some a') (hl : a.link = some l)
    (hs : linksFull[l]? = some sub) (hpc : a.piece = 2 + shift sub)
    (stand : sameStand linksFull a a' = true) (fit : bookFit Dm.N PS told = true)
    (tells : told[k]? = some []) (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (askFresh : Pub.linkFresh l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
    (hbase : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k]?.getD []),
      t.1 < q.base)
    (hSB : ∀ u τ v, (strictAt B' q).ior.red.out u τ = some v → SameBut u.1 v.1)
    (hsmpT : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → Dm.smp (z, s') = Dm.smp (z, s))
    (bPub : ∀ u v : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l (2 + shift sub) → (mgAll Dm Mg).pub p (z, v.1) = true)
    (bPubP : ∀ u v : Desc.First.S × Fr.E.Str,
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a),
        p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1)) :
    BehindPartsR (Fr := Fr) x SET Dm.N (mgAll Dm Mg) linksFull PS z k l (2 + shift sub)
      (Dm.sent.arrayOf.getD l #[]) a a' told
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) :=
  behindParts_ofR (L := Dm.l3) (nsOf := Dm.pubD.nsOf) Dm.G B' z (k3At_mgAll Dm Mg)
    (mgAll_noColl Dm Mg) (mgAll_shown Dm Mg) (fun _ _ => rfl) (fun _ _ => rfl) hns
    (inOrderReads_mgAll Dm Mg hIn) (heldReads_mgAll Dm Mg) hlook hpX here next hl hs hpc stand fit
    tells hfit askFresh hbase
    (fun u τ v h e _ => congrFun (congrFun (hsmpT z u.1 v.1 (hSB u τ v h).st) e.1) e.2)
    bPub bPubP

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attTiesR_mgAll
#print axioms VerifiableInference.OnPublicFiles.layTiesR_mgAll
#print axioms VerifiableInference.OnPublicFiles.behindPartsR_mgAll
