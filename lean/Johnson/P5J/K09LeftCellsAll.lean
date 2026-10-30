-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftCellsAll.lean: K9's LAW AT THE 25 LINKS, AT THE CLOSED CONSTANT: THE SENTENCE
cells OF THE NAMED REST OF THE FIELD hLeft, WITH ALL SEVEN OF ITS PREMISES ON PUBLIC DATA LAID IN:
FROM THE HEAD AND ONE PREMISE ON REACHED STATES. One theorem: a joining, by calls. A law file; no
running text imports it.
  `AtMgA.left_cells_at`  `AtMgA.left_cells` (K09LeftCells.lean beside this file) with hp | hpl
(batch_place) · h3 (AtMgA.left_moments: K09LeftCellsPub.lean) · hT1 | hT2 (
AtMg.hT1_cells, AtMg.hT2_cells: Johnson/P2LawR/CellsAtHead.lean) · hB | hZ (
AtMg.hBZ_cells: Johnson/P2LawR/LaidArrAtHead.lean) laid in. The last four stand at the closed
letters At.…, which are h.𝔇's fields by unfolding: Lean's own word here. LEFT: F: the facts on
reached states (FoldFacts), at the listed seats Ld that At.laid? Zp names (hL): a premise here;
`atMgR_rch_of_head` (StartAtHead.lean) has it from the head.

Limits. AN IMPLICATION.
K09LeftCells.lean's.
Nothing on soundness or on hiding.
-/
import Johnson.P5J.K09LeftCellsPub
import Johnson.P2LawR.CellsAtHead
import Johnson.P2LawR.LaidArrAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S FoldFacts)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.LinkJoin (batchAt onTR)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

open VerifiableInference.Desc in
/-- **cells, with all seven laid in.** -/
theorem AtMgA.left_cells_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Ld : Laid}
    (hL : At.laid? Zp = some Ld)
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW At.links At.ps)
    {m : ℕ} (hm : m < 25) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (At.X Zp) m = some (xx, tlD))
    (z : ProofFile.InstPub) :
    ∀ a pa, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) a → atS.get? a.1 = some pa →
      CellOkR xx tlD h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
        (h.𝔇.N.group m) pa := by
  obtain ⟨p, hp, hpl⟩ := batch_place hm
  have el : xx.link = m := IM.lookAt_link (look_of_dig hd)
  obtain ⟨hB, hZ⟩ := h.toAtMg.hBZ_cells hm hd el h.𝔇.l3.rad
  exact h.left_cells F hm hd hp hpl (h.left_moments m)
    (h.toAtMg.hT1_cells hL hm el hp h.𝔇.l3.rad) (h.toAtMg.hT2_cells Ld hm el hp h.𝔇.l3.rad) hB hZ z

end P5J

#print axioms P5J.AtMgA.left_cells_at
