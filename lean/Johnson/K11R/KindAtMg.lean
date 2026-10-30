-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/K11R/KindAtMg.lean: THE KIND K11's OWN SENTENCE (the merge of the claims on the committed
table) ENDS IN THE FORM IN WHICH A KIND's LAW IS COUNTED: `P5J.AtMgA.Kind h 𝔏 K11`
(Johnson/P5J/RowsAtAll.lean). One theorem: a corollary of `k11_law_atMg` (LawAtMg.lean), by
unfolding.

What is said. `k11_kind`: from the constant's own head h, at every filling 𝔏 of the rows' letters
with the three lists' heads (q₁, q₂, q₃): TWO FACTS ON THE PUBLIC PART, tm (a test with code,
`k11AtRB`: the two members are there) and hc (an equation: the first chain's rows are the written
rows), and K: «at every opening of the IOP as written in Lean at the head's letters, at the two
members that tm gives, there are posI, ni, R, Wa with `K11Cond` at the head's own "reached"» give
`h.Kind 𝔏 K11`.
  The opening, the data and the test on the plan are drawn from the head's field "laid".
  "Reached" is the head's own term `h.toAtMg.rch`: no letter.

Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). NO CONDITION OF `K11Cond`
IS SHOWN HERE; that they can be met together is shown nowhere. hc is no theorem in scope: it follows
from an accept of the test on the rows. Nothing on soundness.

-/
import Johnson.K11R.LawAtMg
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.Walk.Tied (RchAt)
open P5J (AtMgA mgAtAll TS F0T Free)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, IN THE FORM IN WHICH A KIND's LAW IS
COUNTED.** -/
theorem k11_kind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (tm : k11AtRB Zp 24 = true)
    (hc : VerifiableInference.PlanWritten.cutOf (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull)
    (K : ∀ (Bs : ProofFile.PureBase) (base : List (Block S Cl)),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      ∀ (pM : ℕ × ℕ) (xM xI : Mem),
      maskPlace (P5T.planSeats Zp Zp.D.1) Zp.first.shape 24 = some pM →
      xAt (P5J.At.ms Zp Z.lay) pM = some xM →
      xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI →
      ∃ (posI : ℕ → Bool × ℕ × ℕ) (ni R : ℕ) (Wa : S → Prop),
        K11Cond (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h
          Bs h.toAtMg.rch xM xI posI ni R Wa) :
    h.Kind 𝔏 KindName.K11 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hD : (F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth h.scope h.laid]
    exact h.laid.data
  exact k11_law_atMg h O hD h.laid.planOk q₁ q₂ q₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd 𝔏.c₀ P5J.At.tokOf
    h.toAtMg.rch tm hc (K Bs base O)

end K11

#print axioms K11.k11_kind
