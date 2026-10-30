-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Last.lean: the kind "lookup" (K3): THE THREE SHORT STRUCTURES OF `k03_cond_due`
(Johnson/P5J/K03Due.lean), EACH CUT IN TWO: what is paid at the closed constant, and what
is left. General in the parameters; definitions and three re-packings.

Main names:
  `CallsLastR` (tie · othersPub · othersP · rides) · `callsShort_of_last`: with one and own it gives
    `CallsShortR` (Johnson/Desc/Sound/MgAt/K3Short.lean).
  `ObjLastR` (hB · hTests · h6 · hBare) · `objShort_of_last`: with the four facts along the fold,
    pubSent and pubFree it gives `ObjShortR` (Johnson/P5J/K03ObjAt.lean).
  `DigLastR` (othersPub · othersP · rides · hB · hTests · h6) · `digShort_of_last`: with the seven
    facts along the fold, pubFree and hnS it gives `DigShortR` (Johnson/P5J/K03DigAt.lean).

THE FIELDS' AND THE BINDERS' TEXTS ARE THE THREE STRUCTURES' OWN, LAID HERE BY A PROGRAM; Lean holds
each against its original in the three re-packings.

Limits: nothing is paid here. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Due

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

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
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

open VerifiableInference.Desc.First (moreItem)
open VerifiableInference.Desc.First.FillSent (sentIsB sentName)
open VerifiableInference.Desc.First.Att.P (maskMsg)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

open Cb.Fo.Pin

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (tls : ℕ → HTailF2)
  (a : Desc.Place) (k l : ℕ) (x : Desc.First.Look.Place)

set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **What is left at a segment's calls.** -/
structure CallsLastR (tl : HTailF2)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) : Prop where
  /-- test on the public parameters and the layout -/
  tie : linkTieB X Dm.sent Dm.rad3 num idx x.link tl = true
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

theorem callsShort_of_last (tl : HTailF2)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl)
    (one : OneNumber X Dm.sent Dm.rad3 num idx tls x.link seatL Dm.arr id)
    (own : OwnNamed X Dm.sent num tls x.link Dm.arr Dm.ms Dm.N)
    (V : CallsLastR Dm Mg Rch num idx a k l x tl q b') :
    CallsShortR Dm Mg Rch num idx tls a k l x tl q b' :=
  ⟨V.tie, one, own, V.othersPub, V.othersP, V.rides⟩

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (k l : ℕ) (x : Desc.First.Look.Place)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S Desc.Claim)

/-- **What is left of what objects leaves.** -/
structure ObjLastR (Ld : Desc.K12.Door.Laid) (M : List OracleShape) : Prop where
  hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true
  hTests : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
    (Dm.pubD.dS.own x.link) Dm.N PS[k + 1]? Ld M (Dm.N.sent l 0) (Dm.seat3 x.link false) = true
  h6 : oneShapeB Dm.ms = true
  hBare : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f

theorem objShort_of_last (Ld : Desc.K12.Door.Laid) (M : List OracleShape)
    (hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    Desc.K12.Door.atFirstShapes M a.1 = true)
    (pubSent : ∀ (z : P) s, (mgAll Dm Mg).pub (moreItem (sentName l)) (z, s) = true →
    sentIsB Dm.pubD.dS x.link s = true)
    (pubFree : ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
    H2K5.Door.freeAboveB x.ns s = true)
    (V : ObjLastR Dm Mg Rch claim k l x q b' Ld M) :
    ObjShortR Dm Mg Rch claim k l x q b' Ld M :=
⟨V.hB, hLive, hGroups, hSeats, hShapes, pubSent, pubFree, V.hTests, V.h6, V.hBare⟩

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **What is left at a segment's digits.** -/
structure DigLastR (l : ℕ) (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl)
    (nos : Array ℕ) (n : ℕ) (Ld : Desc.K12.Door.Laid) (M : List OracleShape) : Prop where
  othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
    Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)) ++
      pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[(k3K l true)]?.getD [])
        (Desc.First.rowOf linksFull (IM.k3Place l true))),
    k3Like r = false → (mgAll Dm Mg).pub r (z, v.1) = true
  othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
    Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)),
    (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → (mgAll Dm Mg).pubP r (z, v.1)
  rides : RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b'
  hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true
  hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
    (Dm.N.group l) (Dm.l3.seat x.link true) = true
  h6 : oneShapeB Dm.ms = true

theorem digShort_of_last (l : ℕ) (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl)
    (nos : Array ℕ) (n : ℕ) (Ld : Desc.K12.Door.Laid) (M : List OracleShape)
    (hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hLink : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.link = x.link)
    (hNext : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.next = .laterOrClose)
    (hOwn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → a.1.live.frame.own = nos)
    (hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
    a.1.failed = none → Desc.K12.Door.atFirstShapes M a.1 = true)
    (pubFree : ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
    H2K5.Door.freeAboveB n s = true)
    (hnS : n ≤ x.arrays.ns)
    (V : DigLastR Dm Mg Rch l x q b' nos n Ld M) :
    DigShortR Dm Mg Rch l x q b' nos n Ld M :=
⟨V.othersPub, V.othersP, V.rides, V.hB, hLive, hGroups, hLink, hNext, hOwn, hSeats, hShapes,
    pubFree, hnS, V.hTests, V.h6⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.callsShort_of_last
#print axioms VerifiableInference.OnPublicFiles.objShort_of_last
#print axioms VerifiableInference.OnPublicFiles.digShort_of_last
