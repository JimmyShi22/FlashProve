-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftAllG.lean: K9's LAW AT THE 25 LINKS, AT THE CLOSED CONSTANT: THE NAMED REST OF
THE FIELD hLeft, GENERAL IN THE PROMISE (`LeftRestG`, Johnson/Desc/First/Link/Law/LeftOfRestG.lean),
WHOLE, AT THE LETTERS OF WHAT IS LEFT OF K9: ALL NINE SENTENCES LAID IN BY THEIR PAYERS, UNDER FIVE
NAMED PREMISES. One theorem: a joining, by calls. A law file; no running text imports it.
  `AtMgA.leftRestG_at`  LeftRestG at 𝔇 := h.𝔇 · links := fullLinks · pl := At.ps · Rz := RchAt
  h.toAtMg.rch z · k := batchAt fullLinks At.ps m · x := xx · tlD · sT := fun j => h.𝔇.l3.seat
xx.link true j.1 · AT EVERY PROMISE OkR THAT GIVES THE CORE OkCore nU tlD. The field hLeft of either
structure of what is left of the core then follows by one call of hLeftG_of_rest at this value, at
that structure's own promise: the caller's; not typed here. WHO PAYS THE NINE. As in K09LeftAll.lean
beside this file (which stands at the first structure's promise alone), but slots: by the general
slots_of_four and okFour_of_core (Johnson/LPFE1R/SlotsOfFour.lean). WHAT IS LEFT, EACH A NAMED
PREMISE HERE: hL · F (other files have both from the head) · hc (OkR gives its core) · hLo (ON THE
STATE: the lookups' promise K3LeftOn at the shape tlD.f9 in front of the batching: in the form in
which leftD_at ends; not called here) · a fifth: hd (what digAt returns at m).

Limits. AN IMPLICATION: the four are shown of nothing here; that they can be met together is not
tried here.
At OnBytes.secondHashFunction. Nothing on
soundness or on hiding. Nor is hd shown here.
-/
import Johnson.P5J.K09LeftCellsAll
import Johnson.P5J.K09LeftOnesHead
import Johnson.LPFE1R.SlotsOfFour
import Johnson.LPFE1R.ThreePub
import Johnson.LPFE1R.MaskLeftAt
import Johnson.Desc.First.Link.Law.LeftOfRestG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Model OnBytes.Params OnBytes.PscRun
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First (S FoldFacts momentAt shiftAt)
open VerifiableInference.Desc.First.Look (digList)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.LinkJoin (batchAt onTR LeftRestG slots_of_four okFour_of_core
  three_of_dig OkCore FullAt pi8)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place} {β : Type}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

open VerifiableInference.Desc in
/-- **The named rest, whole, at every promise that gives the core.** -/
theorem AtMgA.leftRestG_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Ld : Laid}
    (hL : At.laid? Zp = some Ld)
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW At.links At.ps)
    {m : ℕ} (hm : m < 25) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (At.X Zp) m = some (xx, tlD)) (z : ProofFile.InstPub)
    (u : HTailF2) (ψ : S → β) (OkR : Phi β × Option Pub9 → Prop) (nU : Array ℕ)
    (hc : ∀ q, OkR q → OkCore nU tlD q) {lm : ℕ} {Qf : Fork → Prop}
    (hLo : ∀ a, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) a →
      ∃ first, K3LeftOn S.fork? (fun s : S => s.tl?.bind (·.heard)) tlD.f9 lm first Qf a.1) :
    LeftRestG (F := FrK) h.𝔇 fullLinks At.ps z
      (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (batchAt fullLinks At.ps m) m u ψ
      OkR nU xx tlD (fun j => h.𝔇.l3.seat xx.link true j.1) := by
  have hx := look_of_dig hd
  obtain ⟨set, pp, dg⟩ := h.left_dig hm hd
  exact
    { dig := ⟨set, pp, dg⟩
      maskPub := h.left_maskPub hm hd
      first := h.left_first hm hd
      oneCells := h.left_oneCells_head hm hx tlD
      oneMask := h.left_oneMask_head hm hx
      cells := h.left_cells_at hL F hm hd z
      mask := h.left_mask hL F hm hx z
      three := fun a e tl g ho h9 h12 fxe => by
        obtain ⟨first, Lo⟩ := hLo a ho
        exact three_of_dig u ψ OkR nU tlD hc dg a.1 Lo e tl g h9 h12 fxe
      slots := fun a t e b front Fe tl tl' funs F1 c _ hb h8 h9 _ h13 fxe fxt hlat =>
        slots_of_four (phiAll u ψ) OkR (FullAt nU) u pi8 (fun _ => rfl) (okFour_of_core hc) _ t e b
          front Fe tl tl' funs F1 c hb h8 h9 h13 fxe fxt hlat }

end P5J

#print axioms P5J.AtMgA.leftRestG_at
