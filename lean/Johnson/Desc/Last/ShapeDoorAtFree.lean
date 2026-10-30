-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorAtFree.lean: SH₃ AT THE ONE CLOSED VALUE OF THE TOWER'S FREE LETTERS: the
field SH₃ of `FiveF.tables_fit` (Johnson/P5J/TowerEnd.lean), at `h.toAtMg.freeOf h.𝔇 ML (L0.plmAt …
(Sh.X … 12)) e₁ e₂ e₃ dW wEnd` (of which `h.free` is the instance at the closed ML, e₁, e₂, e₃, dW,
wEnd). Each statement ENDS, by the device `fieldOf` (Johnson/Desc/K14/Law/LedgerAtFree.lean), IN THE
TYPE OF THAT FIELD ITSELF: named through its projection, not copied. Statements with their proofs;
no definition.

Main names (namespace `Desc.K14.Law.ShDoor`: the opens are the neighbouring file's:
SharedConstAtFree.lean).
  **`SH₃_at_free_of`**: the field, from: hZ (the public part is the computed one) · H : `DoorStays
    (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks At.ps Pw V` · hR: inside the first table's last
    promise, under the tower's own `h.toAtMg.rc`, without a mark: `FourFacts V` of the first chain's
    last state · hlen: the shared chain's last border is 12. := `sh₃_field_plm`
    (Johnson/LTPileR/DoorAtPlm.lean); what it asks of the shared table's promise is paid by
    `Sh.door_of_shape` and `Sh.X_of_shape`.
  **`SH₃_at_free`**: the same with H PAID: by `doorStays_mgAll`
    (Johnson/Desc/Last/ShapeDoorAtAll.lean) through `mgAt_is_mq` (RowsAtMg.lean): left of it:
    hi, hw (V's two seats are the numbers' own) and h6, h7 (two counts of answers are 1).

Limits. RULES AT A CLOSED VALUE: NO MEMBER: that one V meets hi, hw, h6, h7 and hR together is shown
in no theorem here; that the head h is met at the release's files is not shown. hR and hlen are
other files' to show (hR: `hR_of_own` of Johnson/LTPileR/FourAtEnd.lean [not in this library] is not imported).
Nothing on soundness or on hiding.

-/
import Johnson.Desc.K14.Law.SharedConstAtFree
import Johnson.Desc.K14.Law.SharedConstShape
import Johnson.Desc.Last.ShapeDoorAtAll
import Johnson.LTPileR.DoorAtPlm
import Johnson.P5J.L0.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open VerifiableInference.OnPublicFiles (kcReq)


variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

open VerifiableInference.Desc.Last (DoorStays FourFacts OwnSeats sh₃_field_plm doorStays_mgAll)

namespace ShDoor

section
variable (h : P5J.AtMgA o Z D r Zp Np cF x)
  (depthReq : ℕ)
  (ML : VerifiableInference.Desc.Last.MeaningL (P5J.F0T o Zp Np cF).S₃
    (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
  (e₁ : (i : ℕ) → (ds : List RDT) → ((P5J.F0T o Zp Np cF).XiPub × (P5J.F0T o Zp Np cF).S₁) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (e₂ : (i : ℕ) → (ds : List RDT) →
      (((P5J.F0T o Zp Np cF).XiPub × (P5J.F0T o Zp Np cF).S₁) × (P5J.F0T o Zp Np cF).S₂) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (e₃ : (i : ℕ) → (ds : List RDT) →
      (((P5J.F0T o Zp Np cF).XiPub × (P5J.F0T o Zp Np cF).S₁ × (P5J.F0T o Zp Np cF).S₂) ×
        (P5J.F0T o Zp Np cF).S₃) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃
        (P5J.F0T o Zp Np cF).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (dW wEnd : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **SH₃ AT THE CLOSED VALUE, H AND hR NAMED.** -/
theorem SH₃_at_free_of {pol lay KL : ByteArray} (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Zp)
    (Pw : Where) (V : OwnSeats)
    (H : DoorStays (P5J.At.N Zp cF) (h.toAtMg.mq h.𝔇) P5J.fullLinks P5J.At.ps Pw V)
    (hR : ∀ (q : ProofFile.InstPub × First.S) (y : Strs),
      ocEnd (fun a : ProofFile.InstPub × First.S => (a.1, a.2)) (P5J.At.N Zp cF) (h.toAtMg.mq h.𝔇)
        P5J.fullLinks P5J.At.ps q y →
      h.toAtMg.rc q → q.2.failed = none → FourFacts V q.2)
    (hlen : 1 + (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).l₂.length = 12) :
    fieldOf (fun V' : h.Five (h.toAtMg.freeOf h.𝔇 ML
        (P5J.L0.plmAt o Zp Np cF (Sh.X h.toAtMg.shPlan 12)) e₁ e₂ e₃ dW wEnd) depthReq =>
      (P5J.FiveF.tables_fit V').SH₃) := by
  intro b s hb hs
  exact sh₃_field_plm o pol lay KL Zp hZ Np cF (LLT25.c2 Np).rounds (fun a => (a.1, a.2))
    (fun _ _ => rfl) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd) _
    (Sh.pm h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)) true (P5J.At.N Zp cF) (h.toAtMg.mq h.𝔇)
    P5J.fullLinks P5J.At.ps Pw V H h.toAtMg.rc hR (Sh.X h.toAtMg.shPlan 12)
    (fun d hd => Sh.door_of_shape h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) d (hlen ▸ hd))
    (fun d hd => Sh.X_of_shape h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) d (hlen ▸ hd))
    (ToldDesc.p14At Zp).codes (ToldDesc.p14At Zp).S b s hb hs

/-- **SH₃ AT THE CLOSED VALUE, H PAID.** -/
theorem SH₃_at_free {pol lay KL : ByteArray} (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Zp)
    (V : OwnSeats) (hi : V.index = (P5J.At.N Zp cF).index) (hw : V.w = (P5J.At.N Zp cF).w)
    (h6 : V.indexShape.answers = 1) (h7 : V.wShape.answers = 1)
    (hR : ∀ (q : ProofFile.InstPub × First.S) (y : Strs),
      ocEnd (fun a : ProofFile.InstPub × First.S => (a.1, a.2)) (P5J.At.N Zp cF) (h.toAtMg.mq h.𝔇)
        P5J.fullLinks P5J.At.ps q y →
      h.toAtMg.rc q → q.2.failed = none → FourFacts V q.2)
    (hlen : 1 + (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).l₂.length = 12) :
    fieldOf (fun V' : h.Five (h.toAtMg.freeOf h.𝔇 ML
        (P5J.L0.plmAt o Zp Np cF (Sh.X h.toAtMg.shPlan 12)) e₁ e₂ e₃ dW wEnd) depthReq =>
      (P5J.FiveF.tables_fit V').SH₃) := by
  have H : DoorStays (P5J.At.N Zp cF) (h.toAtMg.mq h.𝔇) P5J.fullLinks P5J.At.ps
      (h.toAtMg.𝔇 h.𝔇).pubD.P13 V := by
    rw [← P5J.mgAt_is_mq h.toAtMg h.𝔇]
    exact doorStays_mgAll _ _ (P5J.At.N Zp cF) V hi hw h6 h7
  exact SH₃_at_free_of h depthReq ML e₁ e₂ e₃ dW wEnd hZ _ V H hR hlen

end

end ShDoor

end Desc.K14.Law

#print axioms Desc.K14.Law.ShDoor.SH₃_at_free_of
#print axioms Desc.K14.Law.ShDoor.SH₃_at_free
