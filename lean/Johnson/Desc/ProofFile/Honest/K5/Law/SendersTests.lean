-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersTests.lean: one premise's form on the senders' lots. One
definition, no theorem.

  PlanSwitchLotForFillTests   PlanSwitchLotForFill with the closing laid and six tests

Limits.
  * A BAD RESULT. The form keeps the clause «shape.maskRows ≠ 0». Under the head that clause cannot be met
    at the second and third own messages of the switch into segment 2 g, for g from 1 to 11. This is
    argued, not proved. PlanSwitchLotForFillLean (SendersFillLean.lean in this folder) has no such clause.
  * None of the six tests is proved here. hh, the clause on K2.handed, is a clause on the book, run at no book. At the closing the
    form reads K2.lotClosingAt lay segs alone; lay and segs are tied to the head's plan by nothing. D₀, fx
    and ch stand under "there is".
  * A definition: nothing is claimed of it. This file proves nothing about soundness, completeness, hiding
    or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersPlan
import Johnson.Desc.ProofFile.Honest.K5.Law.SwitchAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree
  Covers ofLots_hfix)
open ProofFile.Honest.K1 (cellsVals firstData)
open P5J (AtMgA TS CellsM)

variable {W₀ : Type} {wt : W₀ → Weights} {cellsOf : W₀ → P5J.CellsM OnBytes.Flat.numsFull}

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **`PlanSwitchLotForFill` with the closing laid and six tests for hS.** A premise's form. -/
def PlanSwitchLotForFillTests
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (S : Sz)
    (G : Ground)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (Ad : MsgAddr)
    (l m' : ℕ)
    (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, ∀ m, Ad = p.ownAddr m → l = p.link → ∃ (D₀ : Pub → Ground →
      RowDataOf ProofFile.Inst) (fx ch : ℕ), (⟨P5J.At.num Zp l m', fx, K2.switchMsgTxt ch
            (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay segs) p (1 + p.sizes.kept.length + m)⟩ :
            MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml ∧ LotsAgree ml ⟨P5J.At.num Zp l m', fx,
                  K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay segs) p (1 +
                  p.sizes.kept.length + m)⟩ ∧ 1 + p.sizes.kept.length + m < (K2.switchSent p.sizes
                  p.others).size ∧ 1 + p.sizes.kept.length + m ≠ (K2.switchSent p.sizes p.others).size - 1 ∧
      ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape.maskRows ≠
      0 ∧ (∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K2.switchSeat Zp
      G) fun _ => 0).lays (p.ownAddr m) row place = true → row < ((K2.switchSent p.sizes
      p.others).getD (1 + p.sizes.kept.length + m) default).shape.mainRows ∧ place <
      (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.code default).ell) ∧ K2.closingOk K2.freshTable (segs.take p.link) p = true ∧
      p.sizes.serves = true ∧ p.sizes.roomy = true ∧ K2.placeFits p = true ∧ (∀ k : Coins Bk,
      (K2.handed ch p k).isSome = true) ∧ ∀ w, Vd w → K2.publicOk (K2.withSwitchData S D₀ Zp G) lay
      p (segs.take p.link) w.x = true

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {G : Ground} {B : ProverCoinCounts}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

end ProofFile.Honest.K5

