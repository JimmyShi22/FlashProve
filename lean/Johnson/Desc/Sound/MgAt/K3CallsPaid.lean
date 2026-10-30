-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsPaid.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll, at the border kOfCalls l: (1) THE KIND's LEDGER's FIELD objects (AttOwedR, LayOwedR:
Johnson/Desc/Sound/MgAt/K3Owed.lean), IN THE FIELD's OWN TEXT, WITH WHAT K3's FILES PAY LAID IN:
into objects_att_mgAll_facts, objects_lay_mgAll_facts (MgAt/K3CallsObjFacts.lean): hBare
(calls_hBare_mgAll, MgAt/K3CallsBareAt.lean) and askSent, askFree (asks_behind_mgAll,
MgAt/K3CallsAsks.lean). (2) hmask: "behind the accept the mask row's message has a seat among the
link's own", the premise that the public test formsInT at the runs "objects" and "guests" spends, IN
ITS OWN TEXT, from the four facts along the fold: the message is seated IN FRONT
(maskOkCalls_of_sentIs, Johnson/Desc/First/Look/K3CallsMaskOk.lean, on the state in front), and the
accept leaves the open link's context and the book. By calls alone. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' item formsT l 2 "objects"; the reader maskSeat
  (Johnson/Desc/First/Batch/FormsIn.lean) at the part behind an accept.
Used by K03MaskSeatAt.lean (Johnson/P5J/): hmask_mgAll alone. objects_att_paid and objects_lay_paid
  have no caller.
LETTERS: those of MgAt/K3CallsObjFacts.lean and MgAt/K3CallsOthers.lean.

WHAT IS LEFT, BOOKED: fold fact, at the border in front: hLive, hGroups, hSeats, hShapes · term:
  hmore, hA, hlink, hpass, hfind, hSt · test: hrun (a membership in the table's map of names), hfit
  (pubs), hns (slots), hns0, hsP, hB, hTests (at the border behind; for objects), hTestsF (at the
  border in front; for hmask), hsome, h6, the place's facts.

Main names: `maskSeat_of_ok` · `hmask_mgAll` · `objects_att_paid`, `objects_lay_paid`.

Limits. At Cl := Desc.Claim. Attention and the layers. NOT HERE: the item formsInT l 2 "objects"
itself (the table's name stands for two runs, "objects" and "guests": it is left to other files).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsObjFacts
import Johnson.Desc.Sound.MgAt.K3CallsObjIn
import Johnson.Desc.Sound.MgAt.K3CallsAsks
import Johnson.Desc.Sound.MgAt.K3CallsBareAt

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
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles maskSeat maskAt
  seatAt)
open VerifiableInference.Desc.First (pubAll pubAll_more_sentIs)
open VerifiableInference.Desc.First.FillSent (sentIsB)
open VerifiableInference.Desc.First.Att.P (maskMsg maskOracle_mask)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

/-- **Where the part meets what the law on the mask entries asks, the mask row's message has a seat
among the link's own.** -/
theorem maskSeat_of_ok {x : Desc.First.Look.Place} {D : Sent} {rad : OracleShape → ℕ}
    {seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ} {ms : List Mem} {own : List (ℕ × ℕ)}
    {c : Desc.K9.Part} (hB : maskCallsB D (sigListCalls D rad x.link) x.link x.ns = true)
    (M : MaskOkCalls x D rad seatT ms own c) (h0 : 0 < x.ns) :
    (maskSeat own c).isSome = true := by
  obtain ⟨z, hz, hk, -⟩ := mask_seated hB h0
  obtain ⟨-, -, -, hw⟩ := maskOracle_mask M.frame hz
  obtain ⟨o, ho, hs⟩ := M.seat 0 z h0 hz
  have e : maskAt c.L.check.frame = some o := hw.trans ho
  unfold maskSeat
  rw [e]
  show (seatAt own c.d.book o).isSome = true
  rw [hs hk]
  rfl

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes) (shape : Params.ReqShape)
  {l : ℕ} {x : Desc.First.Look.Place} {a : Desc.Place} {sub : ModelPart}
  {b' : Desc.Block Desc.First.S Desc.Claim}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  {pr : ℕ} {H : LinkHoles} {lk : Link Desc.First.S Desc.Claim}
  {pass : Desc.First.S → Desc.First.S → Prop}
  {Ld : Desc.K12.Door.Laid} {M : List OracleShape}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **hmask, from the facts along the fold.** -/
theorem hmask_mgAll
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2 + shift sub)
    (hl : l < 25) (hsub : linksFull[l]? = some sub) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hmore : Mg.more = {}) (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hns : (Dm.built[l]?).map (·.ns) = some x.ns) (hns0 : 0 < x.ns)
    -- four facts along the fold, at the border in front
    (hLive : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.groups = reqGroups u.1.live.frame.shape)
    (hSeats : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstSeats Ld u.1 = true)
    (hShapes : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstShapes M u.1 = true)
    (hTestsF : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
      (Dm.pubD.dS.own x.link) Dm.N PS[kOfCalls l]? Ld M (Dm.N.sent l 0)
      (fun j => Dm.seat3 x.link false j) = true)
    (hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true)
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨⟨sigListCalls Dm.sent Dm.rad3 x.link, seatL⟩, i⟩)
    (h6 : oneShapeB Dm.ms = true) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ c, segAt? v.1 = some c → (maskSeat (Dm.N.sent l 0) c).isSome = true := by
  intro B' hB' z u v hu hr hf hy c hc
  have e : placeAt X l false = some theP := by
    unfold placeAt
    rw [hlook]
    rfl
  obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
    seat_yes claim readers codes shape h hOk hla hpcX e hback B' hB' u v hy
  have hsb := k3_calls_sameBut claim piece laid before theP guests u.1 v.1 rs cols hd
  have hM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hmore
  have hfront := onQ_front hu hf
  rw [hM] at hfront
  have hIn := calls_onIn_mgAll Dm Mg hfit here hla hsub hpc hpcX hlook z u hu hf
  obtain ⟨F, hF, -, -, -⟩ := k3OnIn_free hsP hIn
  obtain ⟨Lc, hLc⟩ := link_some_of_fork hF
  obtain ⟨a0, ha0, -, -, -, -⟩ := segAt_make hLc hF (tl_some_of_fork hF)
  have hS0 : sentIsB Dm.pubD.dS x.link u.1 = true := by
    have hmem : ∀ sb : ModelPart, Pub.more (some l) "frame.sentIs" ∈ keptCalls l sb := fun sb => by
      cases sb <;> simp [keptCalls]
    have h1 : pubAll Dm.pubD Mg.pub (.more (some l) "frame.sentIs") (z, u.1) = true :=
      hfront (.more (some l) "frame.sentIs") ((calls_sorted hl hsub here).2 _ (hmem sub))
    rw [pubAll_more_sentIs] at h1
    rw [lookAt_link hlook]
    exact h1
  have hFr : H2K5.Door.freeAboveB x.ns u.1 = true := by
    have h1 : ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n u.1) = true :=
      hfront (.freeAbove l) (List.mem_append_left _ (by
        rw [← hM]
        exact calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l sub hfit here hla
          hsub hpc (.freeAbove l) (by simp)))
    have hns' : Dm.pubD.nsOf l = some x.ns := hns
    rw [hns', Option.any_some] at h1
    exact freeAbove_door h1
  have M0 := maskOkCalls_of_sentIs x Dm.sent Dm.rad3 seatL Dm.ms (Dm.N.sent l 0)
    (fun j => Dm.seat3 x.link false j) (fun _ => rfl) (hLive z u hr hf) (hGroups z u hr hf) hS0 hFr
    (Nat.le_refl _) (onQ_book hu hf) (hSeats z u hr hf) (hShapes z u hr hf) hTestsF hsome h6 a0 ha0
  have h0 := maskSeat_of_ok hB M0 hns0
  obtain ⟨c1, -, -, -, c5⟩ := segAt_cut hc
  obtain ⟨d1, -, -, -, d5⟩ := segAt_cut ha0
  have eL : c.L = a0.L := Option.some.inj ((c1.symm.trans hsb.link).trans d1)
  have eB : c.d.book = a0.d.book := by rw [c5, d5, hsb.book]
  unfold maskSeat at h0 ⊢
  rw [eL, eB]
  exact h0

/-- **objects, at an attention link, with what K3's files have paid laid in.** -/
theorem objects_att_paid (A : Attention.Shape) (tl : HTailF2)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .attention) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x)
    (hmore : Mg.more = {}) (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hns : (Dm.built[l]?).map (·.ns) = some x.ns)
    -- four facts along the fold, at the border in front
    (hLive : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.groups = reqGroups u.1.live.frame.shape)
    (hSeats : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstSeats Ld u.1 = true)
    (hShapes : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstShapes M u.1 = true)
    (hTests : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
      (Dm.pubD.dS.own x.link) Dm.N PS[kOfCalls l + 1]? Ld M (Dm.N.sent l 0)
      (fun j => Dm.seat3 x.link false j) = true)
    (hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true)
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨⟨sigListCalls Dm.sent Dm.rad3 x.link, seatL⟩, i⟩)
    (h6 : oneShapeB Dm.ms = true)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hlink : Dm.Rd l = readersOfLink H lk)
    (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hrun : (pr, "objects") ∈ Dm.runs l 2 "objects")
    (hSt : ∀ s Dt j, (Dm.St.at1 s Dt).mask j = Dt.mask j) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x A tl Dm.sent Dm.rad3 seatL Dm.arr
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w :=
  objects_att_mgAll_facts Dm Mg Rch claim (kOfCalls l) l x q b' A tl hB hA hrun hlink hpass hfind
    hSt
    (calls_hBare_mgAll Dm Mg Rch claim a (kOfCalls l) l .attention x q b' readers codes shape h hOk
      hback hlook hla hsub hpc hpcX here hfit)
    hlook hns hLive hGroups hSeats hShapes (asks_behind_mgAll Dm Mg hmore hl).1
    (asks_behind_mgAll Dm Mg hmore hl).2 hTests hsome h6

/-- **objects, at a layers' link.** -/
theorem objects_lay_paid (ql : LayPub) (tl : HTailF2)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .layers) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x)
    (hmore : Mg.more = {}) (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hns : (Dm.built[l]?).map (·.ns) = some x.ns)
    -- four facts along the fold, at the border in front
    (hLive : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.groups = reqGroups u.1.live.frame.shape)
    (hSeats : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstSeats Ld u.1 = true)
    (hShapes : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstShapes M u.1 = true)
    (hTests : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
      (Dm.pubD.dS.own x.link) Dm.N PS[kOfCalls l + 1]? Ld M (Dm.N.sent l 0)
      (fun j => Dm.seat3 x.link false j) = true)
    (hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true)
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨⟨sigListCalls Dm.sent Dm.rad3 x.link, seatL⟩, i⟩)
    (h6 : oneShapeB Dm.ms = true)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hlink : Dm.Rd l = readersOfLink H lk)
    (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hrun : (pr, "objects") ∈ Dm.runs l 2 "objects")
    (hSt : ∀ s Dt j, (Dm.St.at1 s Dt).mask j = Dt.mask j) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x ql tl Dm.sent Dm.rad3 (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w :=
  objects_lay_mgAll_facts Dm Mg Rch claim (kOfCalls l) l x q b' ql tl hB hA hrun hlink hpass hfind
    hSt
    (calls_hBare_mgAll Dm Mg Rch claim a (kOfCalls l) l .layers x q b' readers codes shape h hOk
      hback hlook hla hsub hpc hpcX here hfit)
    hlook hns hLive hGroups hSeats hShapes (asks_behind_mgAll Dm Mg hmore hl).1
    (asks_behind_mgAll Dm Mg hmore hl).2 hTests hsome h6

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.maskSeat_of_ok
#print axioms VerifiableInference.OnPublicFiles.hmask_mgAll
#print axioms VerifiableInference.OnPublicFiles.objects_att_paid
#print axioms VerifiableInference.OnPublicFiles.objects_lay_paid
