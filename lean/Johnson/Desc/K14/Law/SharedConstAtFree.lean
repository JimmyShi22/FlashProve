-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/Desc/K14/Law/SharedConstAtFree.lean: WHAT LIES OF THE SHARED CHAIN AT THE SHARED TABLE's
CONSTANT, CARRIED TO THE VALUE OF THE TOWER's FREE LETTERS (AtMg.freeOf,
Johnson/P5J/FreeShared.lean): the fields of "the three tables fit" (TablesFitR,
Johnson/P5J/TopTablesR.lean) that are the shared table's to pay, ONE BY ONE, EACH ENDING IN THE TYPE
    OF
THAT STRUCTURE's OWN FIELD, named through its projection (fieldOf,
    Johnson/Desc/K14/Law/LedgerAtFree.lean),
not copied. Corollaries: no proof of their own. All from the head h alone, but where said.

  Sh.e_at              the two tables read one list of codes (Sh.hcs_of_read at the head's fields)
  Sh.oneDec_free       Sh.OneDec at the other filling (Sh.oneDec_all along Sh.openAll_is_free)
  Sh.TP_at_free · PW_at_free   "the committed table decodes" forward · "the witness's table is
      pinned"
                       back (Sh.TP_at | PW_at)
  Sh.SH_at_free        the first state passes the book-keeping's test at border 0 (Sh.SH_at)
  Sh.END_at_free       what is open behind the first chain's last place (Sh.hEnd_full)
  Sh.POf_at_free · POb_at_free     o_omega's promise forward and its pin back over the second joint,
                       FROM THE WINDOW hw (a premise: o_omega's tree is one of the shared chain's
                           own
                       that are sent at its last border) (Sh.POf_of_window | POb_of_window)
  Sh.last_at_free      what the promise at the shared chain's last border hands to the last chain
                       (Sh.last_of_on), at the condition on₂ of that value's places at border 12
  Sh.len₁_at_free      the first chain's pieces are as many as the table's places: AT THE SECOND
                       HASH FUNCTION ITSELF (Sh.hlen_all)
NOT HERE: len₂ · len₃ · START · SH₃ · stepQ: other files'.
What is not claimed. No example of the head h in Lean at other files than storedPublicFiles and zGap, at another
hash than secondHashFunction, or at those files' own digest. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.LedgerAtFree
import Johnson.Desc.K14.Law.SharedConstFitR
import Johnson.Desc.K14.Law.SharedConstFitSH
import Johnson.Desc.K14.Law.SharedConstPo
import Johnson.Desc.K14.Law.SharedConstEndAt
import Johnson.Desc.K14.Law.SharedConstLastOn
import Johnson.Desc.AtSeats.ShOneDecAll
import Johnson.Desc.AtSeats.ShJointHalvesAll

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

namespace Sh

/-- The two tables read one list of codes: from the head alone. -/
theorem e_at (h : P5J.AtMgA o Z D r Zp Np cF x) :
    P5J.At.cs Zp = (planAt Zp Np (seatF o Zp Np (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes :=
  hcs_of_read h.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF h.laid.planOk _

/-- OneDec at the other filling. -/
theorem oneDec_free (h : P5J.AtMgA o Z D r Zp Np cF x) :
    OneDec h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) (P5J.F0T o Zp Np cF).start₂ := by
  rw [← openAll_is_free h (e_at h)]
  exact oneDec_all h (e_at h)

section
variable (h : P5J.AtMgA o Z D r Zp Np cF x)
  (depthReq : ℕ)
  (ML : VerifiableInference.Desc.Last.MeaningL (P5J.F0T o Zp Np cF).S₃
    (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
  (PLm : VerifiableInference.Desc.Last.PromMeaningL (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).S₃
    ((P5J.F0T o Zp Np cF).XiPub × (P5J.F0T o Zp Np cF).S₁))
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


/-- **TP.** -/
theorem TP_at_free : fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq
    => (P5J.FiveF.tables_fit V).TP) :=
  TP_at h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) _ _ _ _ (fun _ => rfl) (oneDec_free h)

/-- **PW.** -/
theorem PW_at_free : fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq
    => (P5J.FiveF.tables_fit V).PW) :=
  PW_at h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) _ _ _ _ (fun _ => rfl) (oneDec_free h)

/-- **SH.** -/
theorem SH_at_free : fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq
    => (P5J.FiveF.tables_fit V).SH) :=
  SH_at o Zp Np (Desc.K14.Law.secondAt Zp Np) cF _ _ _ (h.toAtMg.shFirst h.𝔇) _ _ _ _ _
    (H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub)

/-- **END.** -/
theorem END_at_free : fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq
    => (P5J.FiveF.tables_fit V).END) := hEnd_full

/-- **POf**, from the window. -/
theorem POf_at_free (hw : (nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).lo ≤ ((nums h.toAtMg.shPlan
    (h.toAtMg.shOpen h.𝔇)).tenant .oOmega).1 ∧
      ((nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).tenant .oOmega).1 < hiAt (1 + (h.toAtMg.threeOf
          e₁ e₂ e₃ dW wEnd).l₂.length) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).p₂ (h.toAtMg.threeOf e₁
          e₂ e₃ dW wEnd).l₂) :
    fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq =>
        (P5J.FiveF.tables_fit V).POf) :=
  POf_of_window h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) _ _ _ hw

/-- **POb**, from the window. -/
theorem POb_at_free (hw : (nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).lo ≤ ((nums h.toAtMg.shPlan
    (h.toAtMg.shOpen h.𝔇)).tenant .oOmega).1 ∧
      ((nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).tenant .oOmega).1 < hiAt (1 + (h.toAtMg.threeOf
          e₁ e₂ e₃ dW wEnd).l₂.length) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).p₂ (h.toAtMg.threeOf e₁
          e₂ e₃ dW wEnd).l₂) :
    fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq =>
        (P5J.FiveF.tables_fit V).POb) :=
  POb_of_window h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) _ _ _ hw

/-- **What the promise at the last border hands to the last chain.** -/
theorem last_at_free (a) (ha : (h.toAtMg.places h.𝔇 (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW
    wEnd)).on₂ 12 a) :
    (∃ o', ended a.1.2 = some o') ∧ X h.toAtMg.shPlan 12 a.1.2 = true ∧
      VerifiableInference.Desc.Last.doorSharedB h.toAtMg.shPlan.p a.1.2 = true :=
  last_of_on (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₂
      (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).ft₂) h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)
    (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).p₂ (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).l₂ a ha

end

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (depthReq : ℕ)
  (ML : VerifiableInference.Desc.Last.MeaningL (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃
    (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
  (PLm : VerifiableInference.Desc.Last.PromMeaningL (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂ (P5J.F0T
                  OnBytes.secondHashFunction Zp Np cF).S₃
    ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁))
  (e₁ : (i : ℕ) → (ds : List RDT) → ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T
                  OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (e₂ : (i : ℕ) → (ds : List RDT) →
      (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁) × (P5J.F0T
                                  OnBytes.secondHashFunction Zp Np cF).S₂) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (e₃ : (i : ℕ) → (ds : List RDT) →
      (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ × (P5J.F0T
                                  OnBytes.secondHashFunction Zp Np cF).S₂) ×
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (dW wEnd : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)


/-- **len₁**, at the second hash function itself. -/
theorem len₁_at_free : fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd)
    depthReq => (P5J.FiveF.tables_fit V).len₁) :=
  hlen_all h (e_at h) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd)
    (h.toAtMg.ofDesc (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) (P5J.freeOf_q₁ h.toAtMg h.𝔇 ML
        PLm e₁ e₂ e₃ dW wEnd)
      (P5J.freeOf_q₂ h.toAtMg h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd)
      (P5J.freeOf_q₃ h.toAtMg h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd))

end

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.e_at
#print axioms Desc.K14.Law.Sh.oneDec_free
#print axioms Desc.K14.Law.Sh.TP_at_free
#print axioms Desc.K14.Law.Sh.PW_at_free
#print axioms Desc.K14.Law.Sh.SH_at_free
#print axioms Desc.K14.Law.Sh.END_at_free
#print axioms Desc.K14.Law.Sh.POf_at_free
#print axioms Desc.K14.Law.Sh.POb_at_free
#print axioms Desc.K14.Law.Sh.last_at_free
#print axioms Desc.K14.Law.Sh.len₁_at_free
