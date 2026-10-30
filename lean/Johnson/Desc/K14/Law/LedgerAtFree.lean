-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerAtFree.lean: K14_law's TOP PAYS THE FIELD shared_joint_count AT THE
FILLING AT WHICH THE PROOF FILE's TOP IS TAKEN. Theorems.

  fieldOf           the type of a structure's field, named through the projection: so that the
  field is NAMED here and not copied.
  openAll_congr     Sh.openAll at two heads over equal data is one.
  k14_at_open       the shared chain's twelve laws for a batch, at the constant's letters READ
  THROUGH A LETTER O that is Sh.openAll's value: k14_shared_joint_count_closed
  (Johnson/Desc/K14/Law/LedgerSharedJointCountClosed.lean) at DP := D.
  k14_at_free       **the field shared_joint_count of h.Five at 𝔏₀ := h.toAtMg.freeOf h.𝔇 ML PLm e₁
  e₂ e₃ dW wEnd** (Johnson/P5J/RowsAtAll.lean, Johnson/P5J/FreeShared.lean), at h.rch, h.rc,
  depthReq. FOUR PREMISES: the head h · hP1 (the one pin) · hn · hR.
HOW. At 𝔏₀ every letter of the field is read through O := h.toAtMg.shOpen h.𝔇: the numbers, the
meaning, the promise, the step, and the slot's own condition too (P5J.freeOf_own: by rfl). So ONE
equation of letters carries the closed theorem over: Sh.openAll_is_free
(Johnson/Desc/K14/Law/SharedConstOpenAllFree.lean). The head stands at the data D, the field at D.at
frS.P.T.a: the two are one in scope (P5J.LaidAt.atDepth).
What is not claimed. THE FOUR PREMISES: hR (Sh.ReachOwed) and hP1 are paid nowhere here; whether the
head can be met is not shown: NO MEMBER. The other four fields of h.Five. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.SharedConstOpenAllFree
import Johnson.Desc.K14.Law.LedgerSharedJointCountClosed
import Johnson.P5J.RowsAtAll

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

/-- The type of a structure's field, named through its projection. -/
abbrev fieldOf {A T : Prop} (_ : A → T) : Prop := T

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- Sh.openAll at two heads over equal data is one. -/
theorem openAll_congr {D₁ D₂ : WholeD} (eD : D₁ = D₂) (h₁ : P5J.AtMgA o Z D₁ r Zp Np cF x)
    (h₂ : P5J.AtMgA o Z D₂ r Zp Np cF x) (e : P5J.At.cs Zp = (Sh.planAt Zp Np (Sh.seatF o Zp Np
      (Desc.K14.Law.secondAt Zp Np) cF)).Q.codes) : Sh.openAll h₁ e = Sh.openAll h₂ e := by
  subst eD
  rfl

section
variable (h : P5J.AtMgA o Z D r Zp Np cF x)
  (hP1 : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made =
    true) (depthReq : ℕ) (hn : 2 ^ depthReq ≤ 64)
  (hR : Sh.ReachOwed o Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
    VerifiableInference.Desc.K13.Law.LFull)
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

include hP1 hn hR ML PLm in
/-- **The twelve laws, at the constant's letters read through a letter O.** -/
theorem k14_at_open (h' : P5J.AtMgA o Z (D.at frS.P.T.a) r Zp Np cF x)
    (e : P5J.At.cs Zp = (Sh.planAt Zp Np (Sh.seatF o Zp Np (Desc.K14.Law.secondAt Zp Np)
      cF)).Q.codes)
    (O : ShOpen ProofFile.InstPub (ProofFile.InstPub × First.S) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      h.toAtMg.shPlan.Q) (eO : Sh.openAll h' e = O) :
    EachLawsBN
      (keyAt Prod.snd (D.at frS.P.T.a).t₁
        (atDesc (P5J.F0T o Zp Np cF) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd)).p₂
        (atDesc (P5J.F0T o Zp Np cF) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd)).l₂)
      (onQ₂ (Sh.nums h.toAtMg.shPlan O) (Sh.pm h.toAtMg.shPlan O) (Sh.own h.toAtMg.shPlan O) true
        (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).p₂ (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).l₂)
      (stepAt (Sh.nums h.toAtMg.shPlan O) (Sh.mg h.toAtMg.shPlan O) (Sh.pm h.toAtMg.shPlan O)
        (Sh.own h.toAtMg.shPlan O) true (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).p₂
        (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).l₂
        (extOf (Sh.nums h.toAtMg.shPlan O) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).p₂
          (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd).l₂ (Sh.ex h.toAtMg.shPlan O _)))
      (2 ^ depthReq) 0
      ((atDesc (P5J.F0T o Zp Np cF) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd)).p₂ ::
        (atDesc (P5J.F0T o Zp Np cF) (h.toAtMg.threeOf e₁ e₂ e₃ dW wEnd)).l₂) := by
  subst eO
  exact k14_shared_joint_count_closed (fun _ => 0) (fun _ => 0) Zp cF o Z r Np dW wEnd hR D e₁ e₂ e₃
    depthReq hn x h' hP1 (Sh.mg h.toAtMg.shPlan (Sh.openAll h' e)) ML PLm

include hP1 hn hR in
/-- **The field shared_joint_count of P5J.FiveF, at the filling at which the top is taken.** -/
theorem k14_at_free :
    fieldOf (fun V : h.Five (h.toAtMg.freeOf h.𝔇 ML PLm e₁ e₂ e₃ dW wEnd) depthReq =>
      P5J.FiveF.shared_joint_count V) := by
  have eD : D.at frS.P.T.a = D := P5J.LaidAt.atDepth h.scope h.laid
  have h' : P5J.AtMgA o Z (D.at frS.P.T.a) r Zp Np cF x := eD.symm ▸ h
  have e : P5J.At.cs Zp = (Sh.planAt Zp Np (Sh.seatF o Zp Np (Desc.K14.Law.secondAt Zp Np)
      cF)).Q.codes :=
    Sh.hcs_of_read h.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF h.laid.planOk _
  exact k14_at_open h hP1 depthReq hn hR ML PLm e₁ e₂ e₃ dW wEnd h' e (h.toAtMg.shOpen h.𝔇)
    ((openAll_congr eD h' h e).trans (Sh.openAll_is_free h e))

end

end Desc.K14.Law

#print axioms Desc.K14.Law.openAll_congr
#print axioms Desc.K14.Law.k14_at_open
#print axioms Desc.K14.Law.k14_at_free
