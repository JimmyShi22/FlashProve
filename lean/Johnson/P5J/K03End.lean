-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03End.lean: the kind "lookup" (K3): THE THREE STRUCTURES OF `k03_cond_due2`
(Johnson/P5J/K03Last.lean, K03Due2.lean) AND `HeadShortR`, EACH CUT IN TWO: what is paid at the
closed constant, and what is left. General in the parameters; definitions and four
re-packings.

Main names:
  `CallsEndR` (tie · othersPub) · `callsLast_of_end`: with othersP and rides it gives `CallsLastR`.
  `ObjEndR` (hB · hTests · h6: three tests) · `objLast_of_end`: with hBare it gives `ObjLastR`.
  `DigEndR` (othersPub · rides · hB · hTests · h6) · `digLast_of_end`: with othersP it gives
    `DigLastR`.
  `HeadEndR` (model) · `headShort_of_end`: with parts and rides it gives `HeadShortR`
    (Johnson/P5J/K03HeadAt.lean).

THE FIELDS' AND THE BINDERS' TEXTS ARE THE THREE STRUCTURES' OWN, LAID HERE BY A PROGRAM; Lean holds
each against its original in the four re-packings.

Limits: nothing is paid here. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Last

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
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ)
  (a : Desc.Place) (k l : ℕ) (x : Desc.First.Look.Place)

/-- **What is left at a segment's calls.** -/
structure CallsEndR (tl : HTailF2)
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

theorem callsLast_of_end (tl : HTailF2)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl)
    (othersP : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
    onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
    ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[k]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull a),
      p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1))
    (rides : RidesAtR Dm.N (mgAll Dm Mg) Rch k q b')
    (V : CallsEndR Dm Mg Rch num idx a k l x tl q b') :
    CallsLastR Dm Mg Rch num idx a k l x tl q b' :=
  ⟨V.tie, V.othersPub, othersP, rides⟩

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (k l : ℕ) (x : Desc.First.Look.Place)

/-- **What is left of what objects leaves: three tests.** -/
structure ObjEndR (Ld : Desc.K12.Door.Laid) (M : List OracleShape) : Prop where
  hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true
  hTests : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
    (Dm.pubD.dS.own x.link) Dm.N PS[k + 1]? Ld M (Dm.N.sent l 0) (Dm.seat3 x.link false) = true
  h6 : oneShapeB Dm.ms = true

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

theorem objLast_of_end (Ld : Desc.K12.Door.Laid) (M : List OracleShape)
    (hBare : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f)
    (V : ObjEndR Dm k l x Ld M) :
    ObjLastR Dm Mg Rch claim k l x q b' Ld M :=
  ⟨V.hB, V.hTests, V.h6, hBare⟩

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **What is left at a segment's digits.** -/
structure DigEndR (l : ℕ) (x : Desc.First.Look.Place)
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
  rides : RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b'
  hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true
  hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
    (Dm.N.group l) (Dm.l3.seat x.link true) = true
  h6 : oneShapeB Dm.ms = true

theorem digLast_of_end (l : ℕ) (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl)
    (nos : Array ℕ) (n : ℕ) (Ld : Desc.K12.Door.Laid) (M : List OracleShape)
    (othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
    Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
        (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)),
    (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → (mgAll Dm Mg).pubP r (z, v.1))
    (V : DigEndR Dm Mg Rch l x q b' nos n Ld M) :
    DigLastR Dm Mg Rch l x q b' nos n Ld M :=
  ⟨V.othersPub, othersP, V.rides, V.hB, V.hTests, V.h6⟩

end

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning ModelPart shift)
open VerifiableInference.Desc (Wit)


local notation "PS" => Desc.First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

/-- **What is left at the output head's calls: model.** -/
structure HeadEndR {Cl : Type} (claim : Aff → Cl) (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
    (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (arrs : Array (Nat × String)) (pl pl' : Desc.Place)
    (told : List (List Desc.Oracle)) : Prop where
  /-- model -/
  model : ∀ B', SeatOf b' B' → ∀ z : P,
    letI := k3SizesAt X
    letI := k3PolicyAt X
    letI := 𝔇.rq z
    HeadModelR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
      (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun u => Rch (k3K 24 false) ((z, u.1), u.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)

theorem headShort_of_end {Cl : Type} (claim : Aff → Cl) (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
    (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (arrs : Array (Nat × String)) (pl pl' : Desc.Place)
    (told : List (List Desc.Oracle))
    (parts : ∀ B', SeatOf b' B' → ∀ z : P,
    BehindPartsR (Fr := Fr) x (Params.settingOf X.P.frame) 𝔇.N (mgAll 𝔇 Mg) linksFull PS z
      (k3K 24 false) 24 3 arrs pl pl' told
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch (k3K 24 false) ((z, u.1), u.2)))
    (rides : RidesAtR 𝔇.N (mgAll 𝔇 Mg) Rch (k3K 24 false) q b')
    (V : HeadEndR 𝔇 Mg Rch claim seats s₀ x q b' arrs pl pl' told) :
    HeadShortR 𝔇 Mg Rch claim seats s₀ x q b' arrs pl pl' told :=
  ⟨parts, V.model, rides⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.headShort_of_end
#print axioms VerifiableInference.OnPublicFiles.callsLast_of_end
#print axioms VerifiableInference.OnPublicFiles.objLast_of_end
#print axioms VerifiableInference.OnPublicFiles.digLast_of_end
