-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftAll.lean: K9's LAW AT THE 25 LINKS, AT THE CLOSED CONSTANT: THE NAMED REST OF THE
FIELD hLeft (`LeftRest`, Johnson/Desc/First/Link/Law/LeftOfRest.lean), WHOLE, AT THE LETTERS OF WHAT
IS LEFT OF K9: ALL NINE SENTENCES LAID IN BY THEIR PAYERS, UNDER FIVE NAMED PREMISES. One theorem: a
joining, by calls. A law file; no running text imports it.
  `AtMgA.leftRest_at`  LeftRest at 𝔇 := h.𝔇 · links := fullLinks · pl := At.ps · Rz := RchAt
  h.toAtMg.rch z · k := batchAt fullLinks At.ps m · x := xx · tlD · sT := fun j => h.𝔇.l3.seat
xx.link true j.1. The field hLeft's own text then follows by one call of hLeft_of_rest
(LeftOfRest.lean) at this value: the caller's; not typed here. WHO PAYS THE NINE. dig · first ·
maskPub: K09LeftPub.lean · cells: K09LeftCellsAll.lean · oneCells · oneMask:
AtMgA.left_oneCells_head, left_oneMask_head (K09LeftOnesHead.lean) · slots:
slots_at_phiAll (Johnson/LPFE1R/SlotsOfFour.lean) · three: three_of_dig (ThreePub.lean) · mask:
AtMgA.left_mask (MaskLeftAt.lean). WHAT IS LEFT, EACH A NAMED PREMISE HERE: hL · F (the listed
seats; the facts on reached states: other files have both from the head) · hc (the promise Ok gives
its core: OkCore nU tlD) · hLo (ON THE STATE: the lookups' promise K3LeftOn at the shape tlD.f9, at
every state in front of the batching: IN THE FORM IN WHICH leftD_at
(Johnson/P5J/K09LeftD.lean) ENDS: that theorem is not called here: it stands on many files that this
one does not want beneath it) · a fifth: hd (what digAt returns at m).

left_mask pays the
field mask whole; hLo
says "∃ first" in the place of a letter.
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
import Johnson.Desc.First.Link.Law.LeftOfRest

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
open VerifiableInference.Desc.LinkJoin (batchAt onTR LeftRest slots_at_phiAll three_of_dig OkCore)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place} {β : Type}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

open VerifiableInference.Desc in
/-- **The named rest, whole, at the letters of what is left of K9.** -/
theorem AtMgA.leftRest_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Ld : Laid}
    (hL : At.laid? Zp = some Ld)
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW At.links At.ps)
    {m : ℕ} (hm : m < 25) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (At.X Zp) m = some (xx, tlD)) (z : ProofFile.InstPub)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (Ok : Phi β × Option Pub9 → Prop)
    (nU : Array ℕ) (p : Where) (hc : ∀ q, Ok q → OkCore nU tlD q) {lm : ℕ} {Qf : Fork → Prop}
    (hLo : ∀ a, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) a →
      ∃ first, K3LeftOn S.fork? (fun s : S => s.tl?.bind (·.heard)) tlD.f9 lm first Qf a.1) :
    LeftRest (F := FrK) h.𝔇 fullLinks At.ps z
      (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (batchAt fullLinks At.ps m) m L u ψ
      Ok nU p xx tlD (fun j => h.𝔇.l3.seat xx.link true j.1) := by
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
        exact three_of_dig u ψ _ nU tlD (fun q hq => hc q hq.1) dg a.1 Lo e tl g h9 h12 fxe
      slots := fun a t e b front Fe tl tl' funs F1 c _ hb h8 h9 _ h13 fxe fxt hlat =>
        slots_at_phiAll u ψ Ok nU tlD p.rows hc _ t e b front Fe tl tl' funs F1 c hb h8 h9 h13 fxe
          fxt hlat }

end P5J

#print axioms P5J.AtMgA.leftRest_at
