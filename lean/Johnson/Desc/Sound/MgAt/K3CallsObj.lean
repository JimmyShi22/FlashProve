-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsObj.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING mgAll:
THE FIELD objects OF AttRestR, LayRestR AND CallsLeftR (Johnson/Desc/Sound/MgAt/K3CallsRestR.lean,
K3CallsLeftR.lean), TO THE LETTER, out of calls_objects_att, calls_objects_lay
(Johnson/Desc/First/Look/K3CallsObjects.lean): their premise hMg ("the meaning's formsT at the run
objects is the forms' layer's") IS rfl AT mgAll, whose outermost layer is that one. By calls alone.
NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' item formsT l 2 "objects".
Used by K03ObjAt.lean (Johnson/P5J/).
LETTERS: those of MgAt/K3CallsRestR.lean and of K3CallsObjects.lean (pr, H, lk, pass).

WHAT IS LEFT, BOOKED: test: hB (the mask's message is seated), hrun · term: hA, hlink, hpass, hfind,
  hSt (mgAll's readers, runs and stated functions at this link) · accept, with facts along
  the
  fold: hOk (MaskOkCalls at the state behind) · accept: hBare (what the lookup's verifier has heard
  holds bare rows alone).

Main names: `objects_att_mgAll`, `objects_lay_mgAll`.

Limits. At Cl := Desc.Claim (calls_objects_* stand there).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsMean
import Johnson.Desc.First.Look.K3CallsObjects

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
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

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

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
set_option quotPrecheck false in
local notation "seatL" => fun j : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length =>
  Dm.seat3 x.link false j.1

/-- **objects, at an attention link.** -/
theorem objects_att_mgAll (A : Attention.Shape) (tl : HTailF2)
    (hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ Dm.runs l 2 "objects")
    (hlink : Dm.Rd l = readersOfLink H lk) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (Dm.St.at1 s Dt).mask j = Dt.mask j)
    (hOk : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ a', segAt? v.1 = some a' →
        MaskOkCalls x Dm.sent Dm.rad3 seatL Dm.ms (Dm.N.sent l 0) a')
    (hBare : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      attObjects x A tl Dm.sent Dm.rad3 seatL Dm.arr
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w :=
  fun B' hB' z =>
    calls_objects_att x Dm.sent Dm.rad3 SET seatL Dm.arr claim Dm.N (mgAll Dm Mg) Mg linksFull PS z
      k l (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) Dm.ms Dm.Rd Dm.runs Dm.St Dm.after Dm.wt Dm.rw Dm.ah pr H lk
      pass hB A tl hA hrun hlink hpass hfind hSt (fun _ _ _ h => h) (hOk B' hB' z)
      (hBare B' hB' z)

/-- **objects, at a layers' link.** -/
theorem objects_lay_mgAll (ql : LayPub) (tl : HTailF2)
    (hB : maskCallsB Dm.sent (sigListCalls Dm.sent Dm.rad3 x.link) x.link x.ns = true)
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hrun : (pr, "objects") ∈ Dm.runs l 2 "objects")
    (hlink : Dm.Rd l = readersOfLink H lk) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hSt : ∀ s Dt j, (Dm.St.at1 s Dt).mask j = Dt.mask j)
    (hOk : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ a', segAt? v.1 = some a' →
        MaskOkCalls x Dm.sent Dm.rad3 seatL Dm.ms (Dm.N.sent l 0) a')
    (hBare : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      Desc.K3.k3OnOut theP v.1 = true →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      ∀ w, (mgAll Dm Mg).formsT l 2 "objects" (z, v.1) (strsOf Fr v.2) w →
      layObjects x ql tl Dm.sent Dm.rad3 (oWc rows cols) wOfC rows cols seatL Dm.arr msgWc
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard v.1 w :=
  fun B' hB' z =>
    calls_objects_lay x Dm.sent Dm.rad3 SET seatL Dm.arr claim Dm.N (mgAll Dm Mg) Mg linksFull PS z
      k l (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch k ((z, u.1), u.2)) Dm.ms Dm.Rd Dm.runs Dm.St Dm.after Dm.wt Dm.rw Dm.ah pr H lk
      pass hB ql tl (oWc rows cols) wOfC rows cols msgWc hA hrun hlink hpass hfind hSt
      (fun _ _ _ h => h) (hOk B' hB' z) (hBare B' hB' z)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_att_mgAll
#print axioms VerifiableInference.OnPublicFiles.objects_lay_mgAll
