-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsObjFacts.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll: THE FIELD objects (AttOwedR, LayOwedR, AttRestR, LayRestR), TO THE LETTER, WITH ITS PREMISE
ON THE STATE BEHIND PAID: a corollary beside objects_att_mgAll, objects_lay_mgAll
(Johnson/Desc/Sound/MgAt/K3CallsObj.lean): calls_objects_att_facts,
calls_objects_lay_facts (Johnson/Desc/First/Look/K3CallsObjectsAt.lean) at mgAll: hMg is rfl; the
meaning's lemmas at the two public tests "frame.sentIs" and freeAbove are PubAllAt.lean's own
(pubAll_more_sentIs, pubAll_freeAbove); the reader of seats is MgData's seat3. THE FACTS ALONG
THE FOLD ARE PLAIN PREMISES AT THEIR OWN BORDER. By calls alone. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' item formsT l 2 "objects".
Used by K3CallsPaid.lean, K3DigitsFree.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: those of MgAt/K3CallsObj.lean; Ld, M: the two letters of the proximity test's door's facts.

WHAT IS LEFT, BOOKED: fold fact, at the border k: hLive (liveShape) · hGroups (liveGroups) · hSeats
  (seatsCarried) · hShapes (msgShapes) · test: hB · hrun · hns · askSent · askFree · hTests · hsome
  ·
  h6 · hlook · term: hA · hlink · hpass · hfind · hSt · accept: hBare.

Main names: `freeAbove_door` · `objects_att_mgAll_facts`, `objects_lay_mgAll_facts`.

Limits. At Cl := Desc.Claim.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsMean
import Johnson.Desc.First.Look.K3CallsObjectsAt
import Johnson.Desc.First.PubAllAt

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
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles)
open VerifiableInference.Desc.First (pubAll pubAll_more_sentIs moreItem)
open VerifiableInference.Desc.First.FillSent (sentName)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

/-- The table's own test "free above" gives the attention caller's (H2K5.Door.freeAboveB). -/
theorem freeAbove_door {n : ℕ} {s : Desc.First.S} (h : Desc.First.freeAboveB n s = true) :
    H2K5.Door.freeAboveB n s = true := by
  unfold Desc.First.freeAboveB at h
  unfold H2K5.Door.freeAboveB H2K5.Door.freeFromB
  cases hf : s.fork? with
  | none =>
    rw [hf] at h
    cases h
  | some G =>
    rw [hf] at h
    simp only [Option.any_some, Bool.and_eq_true] at h ⊢
    exact ⟨h.2, h.1⟩

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (k l : ℕ) (x : Desc.First.Look.Place)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S Desc.Claim)
  {pr : ℕ} {H : LinkHoles} {lk : Link Desc.First.S Desc.Claim}
  {pass : Desc.First.S → Desc.First.S → Prop}
  {Ld : Desc.K12.Door.Laid} {M : List OracleShape}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **objects, at an attention link, from the facts.** -/
theorem objects_att_mgAll_facts (A : Attention.Shape) (tl : HTailF2)
    (hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ Dm.runs l 2 "objects")
    (hlink : Dm.Rd l = readersOfLink H lk) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (Dm.St.at1 s Dt).mask j = Dt.mask j)
    (hBare : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f)
    (hlook : lookAt X l false = some x)
    (hns : (Dm.built[l]?).map (·.ns) = some x.ns)
    -- four facts along the fold, at the border k
    (hLive : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.groups = reqGroups u.1.live.frame.shape)
    (hSeats : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstSeats Ld u.1 = true)
    (hShapes : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstShapes M u.1 = true)
    -- tests on the table, the numbers and the list of members
    (askSent : moreItem (sentName l) ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k + 1]?.getD [])
    (askFree : Pub.freeAbove l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k + 1]?.getD [])
    (hTests : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
      (Dm.pubD.dS.own x.link) Dm.N PS[k + 1]? Ld M (Dm.N.sent l 0)
      (fun j => Dm.seat3 x.link false j) = true)
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨⟨sigListCalls Dm.sent Dm.rad3 x.link, seatL⟩, i⟩)
    (h6 : oneShapeB Dm.ms = true) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x A tl Dm.sent Dm.rad3 seatL Dm.arr
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w :=
  fun B' hB' z =>
    calls_objects_att_facts x Dm.sent Dm.rad3 SET seatL Dm.arr claim Dm.N (mgAll Dm Mg) Mg linksFull
      PS z
      k l (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) Dm.ms Dm.Rd Dm.runs Dm.St Dm.after Dm.wt Dm.rw Dm.ah pr H lk
      pass hB A tl
      hA hrun hlink hpass hfind hSt (fun _ _ _ h => h) (hBare B' hB' z)
      (fun j => Dm.seat3 x.link false j) (fun _ => rfl) (hLive z) (hGroups z) (hSeats z)
      (hShapes z) askSent
      (fun s h => by
        have h1 : pubAll Dm.pubD Mg.pub (.more (some l) "frame.sentIs") (z, s) = true := h
        rw [pubAll_more_sentIs] at h1
        rw [lookAt_link hlook]
        exact h1)
      askFree
      (fun s h => by
        have h1 : ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n s) = true := h
        have hns' : Dm.pubD.nsOf l = some x.ns := hns
        rw [hns', Option.any_some] at h1
        exact freeAbove_door h1)
      hTests hsome h6

/-- **objects, at a layers' link, from the facts.** -/
theorem objects_lay_mgAll_facts (ql : LayPub) (tl : HTailF2)
    (hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ Dm.runs l 2 "objects")
    (hlink : Dm.Rd l = readersOfLink H lk) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (Dm.St.at1 s Dt).mask j = Dt.mask j)
    (hBare : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f)
    (hlook : lookAt X l false = some x)
    (hns : (Dm.built[l]?).map (·.ns) = some x.ns)
    -- four facts along the fold, at the border k
    (hLive : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → u.1.live.frame.groups = reqGroups u.1.live.frame.shape)
    (hSeats : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstSeats Ld u.1 = true)
    (hShapes : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch k ((z, u.1), u.2) →
      u.1.failed = none → Desc.K12.Door.atFirstShapes M u.1 = true)
    -- tests on the table, the numbers and the list of members
    (askSent : moreItem (sentName l) ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k + 1]?.getD [])
    (askFree : Pub.freeAbove l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k + 1]?.getD [])
    (hTests : maskTestsB (maskMsg Dm.sent x.link) (Desc.First.Look.keptAt Dm.sent x.link).length
      (Dm.pubD.dS.own x.link) Dm.N PS[k + 1]? Ld M (Dm.N.sent l 0)
      (fun j => Dm.seat3 x.link false j) = true)
    (hsome : ∀ i, ∃ y ∈ Dm.ms, Alike y ⟨⟨sigListCalls Dm.sent Dm.rad3 x.link, seatL⟩, i⟩)
    (h6 : oneShapeB Dm.ms = true) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x ql tl Dm.sent Dm.rad3 (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w :=
  fun B' hB' z =>
    calls_objects_lay_facts x Dm.sent Dm.rad3 SET seatL Dm.arr claim Dm.N (mgAll Dm Mg) Mg linksFull
      PS z
      k l (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) Dm.ms Dm.Rd Dm.runs Dm.St Dm.after Dm.wt Dm.rw Dm.ah pr H lk
      pass hB ql tl (oWc rows cols) wOfC rows cols msgWc
      hA hrun hlink hpass hfind hSt (fun _ _ _ h => h) (hBare B' hB' z)
      (fun j => Dm.seat3 x.link false j) (fun _ => rfl) (hLive z) (hGroups z) (hSeats z)
      (hShapes z) askSent
      (fun s h => by
        have h1 : pubAll Dm.pubD Mg.pub (.more (some l) "frame.sentIs") (z, s) = true := h
        rw [pubAll_more_sentIs] at h1
        rw [lookAt_link hlook]
        exact h1)
      askFree
      (fun s h => by
        have h1 : ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n s) = true := h
        have hns' : Dm.pubD.nsOf l = some x.ns := hns
        rw [hns', Option.any_some] at h1
        exact freeAbove_door h1)
      hTests hsome h6

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.freeAbove_door
#print axioms VerifiableInference.OnPublicFiles.objects_att_mgAll_facts
#print axioms VerifiableInference.OnPublicFiles.objects_lay_mgAll_facts
