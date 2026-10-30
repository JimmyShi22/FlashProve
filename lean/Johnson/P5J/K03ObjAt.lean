-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03ObjAt.lean: THE KIND "LOOKUP" (K3): THE FIELD objects OF WHAT IS LEFT AT THE 24 LOOKUPS ON A SEGMENT's CALLS (AttShortR | LayShortR, Johnson/Desc/Sound/MgAt/K3Short.lean), AT THE CONSTANT, by objects_att_mgAll | objects_lay_mgAll (Johnson/Desc/Sound/MgAt/K3CallsObj.lean) and maskOkCalls_of_facts (Johnson/Desc/First/Look/K3CallsMaskOkAt.lean), WITH WHAT IS STILL LEFT AS ONE STRUCTURE's FIELDS. A joining.

 (A) CLOSED FACTS ON THE TABLE, BY THE KERNEL (in the manner of Johnson/Desc/Sound/MgAt/K3Tests.lean): callsAskB l: behind the calls' place of segment l the two items "frame.sentIs" l and freeAbove l are open · callsAsk_mgMore: at all 24 · callsAsk_control: a negative test (at the chain's start the first is not open) · askCalls_mgAll.
 (B) THE SENT DATA ARE A CLOSED TERM OF THE PARAMETERS: dS := Dm.pubD.dS. That the composed meaning's public test at "frame.sentIs" l IS sentIsB Dm.pubD.dS l WAS TRIED AS rfl: Lean's elaborator: "not a definitional equality" (in pubAll seven layers stand above that one): WHY is not looked into: it stays a field (pubSent); meant payer: the composed meaning's "every other item is handed on" lemmas, layer by layer.
 (C) ObjShortR Dm Mg Rch claim k l x q b' Ld M : Prop: TEN FIELDS, in the two theorems' own texts: hB (a test on the mask's message) · hLive · hGroups · hSeats · hShapes (four facts on every reached state) · pubSent · pubFree · hTests (a test on the list of rounds) · h6 (a test on the members) · hBare ("the rows that the lookup's verifier has heard are bare").
     AttObjR | LayObjR: the field's sentence, as the lookups' two theorems end (lifted by program).
     hOk_of_short: the premise hOk of the two theorems.
 (D) k03_objects_att | k03_objects_lay: UNDER h : AtMgA OnBytes.secondHashFunction … AND ObjShortR: THE FIELD objects at 𝔇 := h.toAtMg.𝔇 h.𝔇 · mgBase · h.toAtMg.rch · K3Lot.ofForm · k := k3K l false.
  PAID INSIDE: hA (k03_atS2_calls) · hrun · hlink · hpass · hfind · hSt (Johnson/P5J/K03ObjTerms.lean) · hOk's hT (rfl) · askSent · askFree (A) · lookAt X l false = some x (the lookups' attAt_letters | layAt_letters, in scope) and "some" (k03_calls_seats, from the head).
  Ld · M STAY LETTERS; MEANT (BY READING; NOT CHECKED HERE, NOT EVALUATED): Ld := L with At.laid? Zp = some L · M := the planner's first chain's oracle messages' shapes: ONE CHOICE FOR hSeats | hShapes AND hTests TOGETHER.
Limits. ObjShortR is a premise: no member is shown. The head is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03ObjTerms
import Johnson.P5J.K03SeatsAt
import Johnson.P5J.K03PiecesAt
import Johnson.Desc.Sound.MgAt.K3CallsOwedScope
import Johnson.Desc.First.Look.K3PlanLetters
import Johnson.Desc.First.Look.K3PlanLettersLay
import Johnson.Desc.Sound.MgAt.K3CallsObj
import Johnson.Desc.First.Look.K3CallsMaskOkAt
import Johnson.Desc.Sound.MgAt.K3Tests

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

/-- Behind the calls' place of segment l the two items are open. -/
def callsAskB (l : ℕ) : Bool :=
  ((pubSets mgMore linksFull PS)[k3K l false + 1]?.getD []).contains (moreItem (sentName l)) &&
    ((pubSets mgMore linksFull PS)[k3K l false + 1]?.getD []).contains (.freeAbove l)

set_option maxRecDepth 1000000 in
theorem callsAsk_mgMore : (List.range 24).all callsAskB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: at the chain's start "frame.sentIs" 0 is not open. -/
theorem callsAsk_control :
    ((pubSets mgMore linksFull PS)[0]?.getD []).contains (moreItem (sentName 0)) = false := by
  decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (k l : ℕ) (x : Desc.First.Look.Place)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S Desc.Claim)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

theorem askCalls_mgAll (h : Mg.more = {}) (l : ℕ) (hl : l < 24) :
    moreItem (sentName l) ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k3K l false + 1]?.getD [] ∧
      Pub.freeAbove l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k3K l false + 1]?.getD [] := by
  rw [mgAll_more_closed Dm Mg h]
  have h0 := List.all_eq_true.1 callsAsk_mgMore l (List.mem_range.2 hl)
  unfold callsAskB at h0
  simpa using h0

/-- **What is left of the field objects at a lookup on a segment's calls.** -/
structure ObjShortR (Ld : Desc.K12.Door.Laid) (M : List OracleShape) : Prop where
  hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true
  hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.shape = Dm.sent.shape
  hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.groups = reqGroups a.1.live.frame.shape
  hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    Desc.K12.Door.atFirstSeats Ld a.1 = true
  hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch k ((z, a.1), a.2) → a.1.failed = none →
    Desc.K12.Door.atFirstShapes M a.1 = true
  pubSent : ∀ (z : P) s, (mgAll Dm Mg).pub (moreItem (sentName l)) (z, s) = true →
    sentIsB Dm.pubD.dS x.link s = true
  pubFree : ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
    H2K5.Door.freeAboveB x.ns s = true
  hTests : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
    (Dm.pubD.dS.own x.link) Dm.N PS[k + 1]? Ld M (Dm.N.sent l 0) (Dm.seat3 x.link false) = true
  h6 : oneShapeB Dm.ms = true
  hBare : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f

/-- The field's sentence at an attention segment, as objects_att_mgAll ends. -/
abbrev AttObjR (A : Attention.Shape) (tl : HTailF2) : Prop :=
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x A tl Dm.sent Dm.rad3 seatL Dm.arr
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w

/-- The field's sentence at a feed-forward segment, as objects_lay_mgAll ends. -/
abbrev LayObjR (ql : LayPub) (tl : HTailF2) : Prop :=
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x ql tl Dm.sent Dm.rad3 (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (l : ℕ) (x : Desc.First.Look.Place)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S Desc.Claim)

set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **The premise hOk of the two theorems, from what is left.** -/
theorem hOk_of_short (hM : Mg.more = {}) (hl : l < 24)
    {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨callsSending x Dm.sent Dm.rad3 seatL, i⟩)
    (S : ObjShortR Dm Mg Rch claim (k3K l false) l x q b' Ld M) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l false) u →
      Rch (k3K l false) ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l false + 1) v →
      ∀ a', segAt? v.1 = some a' →
        MaskOkCalls x Dm.sent Dm.rad3 seatL Dm.ms (Dm.N.sent l 0) a' :=
  fun B' _ z =>
    maskOkCalls_of_facts (N := Dm.N) (Mg := mgAll Dm Mg) (links := linksFull) (ps := PS) (pi := z)
      (k := k3K l false) x Dm.sent Dm.rad3 seatL Dm.ms (Dm.N.sent l 0) l
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch (k3K l false) ((z, u.1), u.2)) (dS := Dm.pubD.dS)
      (Dm.seat3 x.link false) (fun _ => rfl) (S.hLive z) (S.hGroups z) (S.hSeats z) (S.hShapes z)
      (askCalls_mgAll Dm Mg hM l hl).1
      (S.pubSent z)
      (askCalls_mgAll Dm Mg hM l hl).2 (S.pubFree z) S.hTests hsome S.h6

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

/-- **THE FIELD objects AT AN ATTENTION SEGMENT, AT THE CONSTANT.** -/
theorem k03_objects_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape) {l : ℕ} (hl : l < 25)
    {y : VerifiableInference.Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt (At.X Zp) l = some (y, A, tl)) (q) (b')
    (S : ObjShortR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' Ld M) :
    AttObjR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' A tl := by
  have ho := attAt_odd hx
  have hlook : VerifiableInference.Desc.First.Look.lookAt (At.X Zp) l false = some y := by
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    exact (VerifiableInference.Desc.First.Look.attAt_letters h.toAtMg.scope h.toAtMg.reads
      h.toAtMg.pubOne (by omega) hx).2.2.2
  have hs : At.links[l]? = some .attention := by
    interval_cases l <;> first | rfl | omega
  obtain ⟨lk, -, hlink, nm, run, hfd, hov⟩ := k03_hfind h l hl false
  have hrun := (k03_hrun h l _ hs).1
  rw [← (k03_ix l hl _ hs).1] at hrun
  exact objects_att_mgAll
    (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
    (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b'
    (pass := passR) A tl S.hB k03_atS2_calls hrun hlink k03_hpass ⟨nm, run, hfd, hov⟩ (k03_hSt h)
    (hOk_of_short
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm l y q b' k03_hM (by omega)
      (k03_calls_seats h hl hlook).1 S) S.hBare

/-- **THE FIELD objects AT A FEED-FORWARD SEGMENT, AT THE CONSTANT.** -/
theorem k03_objects_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape) {l : ℕ} (hl : l < 25)
    {y : VerifiableInference.Desc.First.Look.Place} (hx : layAt (At.X Zp) l = some y)
    (ql : LayPub) (tl : HTailF2) (q) (b')
    (S : ObjShortR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' Ld M) :
    LayObjR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b' ql tl := by
  obtain ⟨hp4, hN, -, -⟩ :=
    _root_.Meaning.scope_plans h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have he := layAt_even hp4 hN hx
  have hlook : VerifiableInference.Desc.First.Look.lookAt (At.X Zp) l false = some y := by
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by have := he.1; omega⟩
    exact (VerifiableInference.Desc.First.Look.layAt_letters h.toAtMg.scope h.toAtMg.reads
      h.toAtMg.pubOne (by omega) hx).1
  have hs : At.links[l]? = some .layers := by
    obtain ⟨h1, h2⟩ := he
    interval_cases l <;> first | rfl | omega
  obtain ⟨lk, -, hlink, nm, run, hfd, hov⟩ := k03_hfind h l hl false
  have hrun := (k03_hrun h l _ hs).1
  rw [← (k03_ix l hl _ hs).1] at hrun
  exact objects_lay_mgAll
    (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
    (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q b'
    (pass := passR) ql tl S.hB k03_atS2_calls hrun hlink k03_hpass ⟨nm, run, hfd, hov⟩ (k03_hSt h)
    (hOk_of_short
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm l y q b' k03_hM
      (by have := he.2; omega) (k03_calls_seats h hl hlook).1 S) S.hBare

end P5J

#print axioms VerifiableInference.OnPublicFiles.callsAsk_mgMore
#print axioms VerifiableInference.OnPublicFiles.callsAsk_control
#print axioms VerifiableInference.OnPublicFiles.hOk_of_short
#print axioms P5J.k03_objects_att
#print axioms P5J.k03_objects_lay
