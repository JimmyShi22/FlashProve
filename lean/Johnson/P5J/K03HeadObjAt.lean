-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03HeadObjAt.lean: THE KIND "LOOKUP" (K3): THE FIELD objects OF WHAT IS LEFT AT THE OUTPUT HEAD's CALLS (HeadLeftR, Johnson/Desc/First/Look/K3HeadRestR.lean), AT THE LETTERS AT WHICH HeadRestR.left HAS IT (Johnson/Desc/Sound/MgAt/K3Mean.lean), AT THE CONSTANT: by one call of calls_objects_head (Johnson/Desc/First/Look/K3HeadObjects.lean). k03_headLeft_objects: Lean's own word that the sentence IS the field. A joining.
  callsAsk_head: BY THE KERNEL: behind the head's calls' place (segment 24) the two items "frame.sentIs" 24 and freeAbove 24 are open (callsAskB, Johnson/P5J/K03ObjAt.lean).
  hOk_head_of_short: the premise hOk (MaskOkCalls at the state behind), by maskOkCalls_of_facts, as at the other 24.
  k03_objects_head: UNDER h : AtMgA OnBytes.secondHashFunction …, headAt X = some x (THE LEDGER's OWN x: by report it is lookAt's place with the shape that the calls fix: no equation of the two places can be had in general) AND ObjShortR AT (k3K 24 false, 24, x) (THE SAME STRUCTURE AS AT THE OTHER 24: ten fields): THE FIELD.
  k03_headLeft_objects: that sentence, laid as the field objects into a value of HeadLeftR at HeadRestR.left's letters under its three instances, TYPES: so it is the field to the letter for Lean (and the sentence reads none of the three instances: it is stated without them).
  PAID INSIDE: hA · hrun (the head's sort: (2, "objects") among runs 24 3 "objects") · hlink · hpass · hfind · hSt · hMg (fun _ _ _ h => h) · askSent · askFree · "some".
Limits. ObjShortR is a premise: no member is shown. The head is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03ObjAt
import Johnson.Desc.First.Look.K3HeadObjects
import Johnson.Desc.Sound.MgAt.K3Mean
import Johnson.Desc.Sound.MgAt.K3HeadR
import Johnson.P5J.RowsAtMg

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

local notation "PS" => Desc.First.flatPlacesOf linksFull true

set_option maxRecDepth 1000000 in
theorem callsAsk_head : callsAskB 24 = true := by decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (x : Desc.First.Look.Place)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S Desc.Claim)

set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

theorem askCalls_head_mgAll (h : Mg.more = {}) :
    moreItem (sentName 24) ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k3K 24 false + 1]?.getD [] ∧
      Pub.freeAbove 24 ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k3K 24 false + 1]?.getD [] := by
  rw [mgAll_more_closed Dm Mg h]
  have h0 := callsAsk_head
  unfold callsAskB at h0
  simpa using h0

/-- **The premise hOk at the output head's calls.** -/
theorem hOk_head_of_short (hM : Mg.more = {}) {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨callsSending x Dm.sent Dm.rad3 seatL, i⟩)
    (S : ObjShortR Dm Mg Rch claim (k3K 24 false) 24 x q b' Ld M) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K 24 false) u →
      Rch (k3K 24 false) ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K 24 false + 1) v →
      ∀ a', segAt? v.1 = some a' →
        MaskOkCalls x Dm.sent Dm.rad3 seatL Dm.ms (Dm.N.sent 24 0) a' :=
  fun B' _ z =>
    maskOkCalls_of_facts (N := Dm.N) (Mg := mgAll Dm Mg) (links := linksFull) (ps := PS) (pi := z)
      (k := k3K 24 false) x Dm.sent Dm.rad3 seatL Dm.ms (Dm.N.sent 24 0) 24
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch (k3K 24 false) ((z, u.1), u.2)) (dS := Dm.pubD.dS)
      (Dm.seat3 x.link false) (fun _ => rfl) (S.hLive z) (S.hGroups z) (S.hSeats z) (S.hShapes z)
      (askCalls_head_mgAll Dm Mg hM).1 (S.pubSent z) (askCalls_head_mgAll Dm Mg hM).2 (S.pubFree z)
      S.hTests hsome S.h6

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
  (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- **THE FIELD objects AT THE OUTPUT HEAD's CALLS, AT THE CONSTANT.** -/
theorem k03_objects_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape)
    {x : VerifiableInference.Desc.First.Look.Place}
    (hx : VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some x)
    (q) (b')
    (S : ObjShortR (Fr := FrD)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K 24 false) 24 x q b' Ld M) :
    ∀ B', SeatOf b' B' → ∀ z : ProofFile.InstPub,
      ∀ (a b : VerifiableInference.Desc.First.S × (FrD).E.Str) w,
        onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
          (k3K 24 false) a →
        h.toAtMg.rch (k3K 24 false) ((z, a.1), a.2) → a.1.failed = none →
        (∃ τ, (strictAt B' q).ior.red.out a τ = some b) → SameBut a.1 b.1 →
        VerifiableInference.Desc.K3.k3OnOut
          (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x)
          b.1 = true →
        onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
          (k3K 24 false + 1) b →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).formsT 24 3 "objects" (z, b.1) (strsOf (FrD) b.2) w →
        K3Objects (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm).fork
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm).heard x.fs x.lm x.F.next
          (headNu (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl (h.toAtMg.𝔇 h.𝔇).sent
            (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW (h.toAtMg.𝔇 h.𝔇).l3.wOf
            (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
            (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
            (h.toAtMg.𝔇 h.𝔇).l3.msgW) b.1 w := by
  intro B' hB' z
  have hs : At.links[24]? = some .head := rfl
  have e24 : x.link = 24 := (headAt_link hx).trans
    (headLink_in_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne)
  have hsm := At.calls_some Zp Z.lay x
    (At.k3SeatsB_at Zp cF Z.lay h.k3 x.link (by rw [e24]; decide)).2.2.1
  obtain ⟨lk, -, hlink, nm, run, hfd, hov⟩ := k03_hfind h 24 (by omega) false
  have hrun := (k03_hrun h 24 _ hs).1
  rw [← (k03_ix 24 (by omega) _ hs).1] at hrun
  exact calls_objects_head (Fr := FrD) x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
    (Params.settingOf (At.X Zp).P.frame) (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1)
    (h.toAtMg.𝔇 h.𝔇).l3.arr K3Lot.ofForm (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) _
    linksFull PS z (k3K 24 false) 24 (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
    (fun u => h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2)) (h.toAtMg.𝔇 h.𝔇).ms
    (h.toAtMg.𝔇 h.𝔇).Rd (h.toAtMg.𝔇 h.𝔇).runs (h.toAtMg.𝔇 h.𝔇).St (h.toAtMg.𝔇 h.𝔇).after
    (h.toAtMg.𝔇 h.𝔇).wt (h.toAtMg.𝔇 h.𝔇).rw (h.toAtMg.𝔇 h.𝔇).ah (IM.k3Ix 24 false) _ lk passR
    (k3AdrAt (At.X Zp)) (At.X Zp).H.tl (h.toAtMg.𝔇 h.𝔇).l3.oW (h.toAtMg.𝔇 h.𝔇).l3.wOf
    (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc (h.toAtMg.𝔇 h.𝔇).l3.msgW S.hB
    k03_atS2_calls hrun hlink k03_hpass ⟨nm, run, hfd, hov⟩ (k03_hSt h) (fun _ _ _ hh => hh)
    (hOk_head_of_short (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm x q b' k03_hM
      hsm S B' hB' z)
    (S.hBare B' hB' z)

/-- **LEAN's OWN WORD THAT THE SENTENCE ABOVE IS THE FIELD**: laid as the field objects into a value of
HeadLeftR at HeadRestR.left's letters (under its three instances), it types. -/
theorem k03_headLeft_objects (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape)
    {x : VerifiableInference.Desc.First.Look.Place}
    (hx : VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some x)
    (q) (b')
    (S : ObjShortR (Fr := FrD)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K 24 false) 24 x q b' Ld M)
    (seats : List (ℕ × ℕ)) (s₀ : VerifiableInference.Desc.First.S) (B') (hB' : SeatOf b' B')
    (z : ProofFile.InstPub)
    (H : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      letI := (h.toAtMg.𝔇 h.𝔇).rq z
      HeadLeftR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).G (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl
        (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
        (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
        (Params.settingOf (At.X Zp).P.frame)
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
        (smpCalls seats (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.seat x)
        (Stored.smpWc (rows := numsFull.rows) (cols := colsAt numsFull))
        (Stored.strWc (h.toAtMg.𝔇 h.𝔇).decT s₀ z) (h.toAtMg.𝔇 h.𝔇).l3.msgW k3QAny
        (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
        (fun u => h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2)) K3Lot.ofForm (h.toAtMg.𝔇 h.𝔇).N
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS z (k3K 24 false) 24
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)) :
    letI := k3SizesAt (At.X Zp)
    letI := k3PolicyAt (At.X Zp)
    letI := (h.toAtMg.𝔇 h.𝔇).rq z
    HeadLeftR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).G (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl
      (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
      (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
      (Params.settingOf (At.X Zp).P.frame)
      (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
      (smpCalls seats (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.seat x)
      (Stored.smpWc (rows := numsFull.rows) (cols := colsAt numsFull))
      (Stored.strWc (h.toAtMg.𝔇 h.𝔇).decT s₀ z) (h.toAtMg.𝔇 h.𝔇).l3.msgW k3QAny
      (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
      (fun u => h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2)) K3Lot.ofForm (h.toAtMg.𝔇 h.𝔇).N
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS z (k3K 24 false) 24
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) := by
  letI := k3SizesAt (At.X Zp)
  letI := k3PolicyAt (At.X Zp)
  letI := (h.toAtMg.𝔇 h.𝔇).rq z
  exact { H with objects := k03_objects_head h Ld M hx q b' S B' hB' z }

end P5J

#print axioms P5J.k03_headLeft_objects
#print axioms VerifiableInference.OnPublicFiles.callsAsk_head
#print axioms VerifiableInference.OnPublicFiles.hOk_head_of_short
#print axioms P5J.k03_objects_head
