-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersPlan.lean: two premises' forms on the senders' lots. Two
definitions, no theorem.

  OpeningLotForFill      a lot with the opening's text, in the list, for K5's triple at a filling's address
                         of segment 0. A type and a letter of the sender's job stand under "there is"
  PlanSwitchLotForFill   at every member of the plan's list of switch places that fits: a lot with its
                         text, in the list, for K5's triple at a filling's address

Limits.
  * A BAD RESULT. PlanSwitchLotForFill keeps the clause «shape.maskRows ≠ 0», which under the head cannot
    be met at the second and third own messages of the switch into segment 2 g, for g from 1 to 11. This
    is argued, not proved.
  * Where no member of the list fits, PlanSwitchLotForFill holds emptily; if two fit it asks a lot for
    each. hBk says that the book covers what is due, not that it equals it, and is run at no book.
  * No code names these two definitions: the file stands for SendersTests.lean's imports alone.
  * Definitions: nothing is claimed of them. This file proves nothing about soundness, completeness, hiding
    or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsSendersNine
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceAtFullIn
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoinedTwoBook
import Johnson.Desc.ProofFile.Honest.K5.Law.Eight
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskSwitchBook
import Johnson.Desc.ProofFile.Honest.K5.Law.FillSwitch
import Johnson.Desc.ProofFile.Honest.K5.Law.FillOpening
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatedSwitch

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
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA TS CellsM)

variable {W₀ : Type} {wt : W₀ → Weights} {cellsOf : W₀ → P5J.CellsM OnBytes.Flat.numsFull}

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **A lot with the opening's text, in the list, for K5's triple at a filling's address of segment
0.** A premise's form. A type and a letter of the sender's job stand under "there is". -/
def OpeningLotForFill
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (S : Sz)
    (G : Ground)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (Ad : MsgAddr)
    (m' : ℕ) :
    Prop := ∃ (X : Type) (own₀ : X) (fx ch : ℕ), (⟨P5J.At.num Zp 0 m', fx, K1.msgTxt ch rd
      (K1.firstJob (X := X) S Zp G) own₀ Ad.msg⟩ : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml ∧
      LotsAgree ml ⟨P5J.At.num Zp 0 m', fx, K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀
      Ad.msg⟩ ∧ (shapeAt (K1.firstJob (X := X) S Zp G).P Ad.msg).answers ≠ 0 ∧ (∀ row place,
      (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K1.firstSeat h.𝔇.sent.shape 0) fun
      _ => 0).lays ⟨K1.firstAddr, Ad.msg⟩ row place = true → row < (shapeAt (K1.firstJob (X := X) S
      Zp G).P Ad.msg).mainRows ∧ place < ((K1.firstJob (X := X) S Zp G).P.codes.base.getD (shapeAt
      (K1.firstJob (X := X) S Zp G).P Ad.msg).code default).ell ∧ (row, place) ∉ padInMain
      ((K1.firstJob (X := X) S Zp G).P.codes.base.getD (shapeAt (K1.firstJob (X := X) S Zp G).P
      Ad.msg).code default).ell (shapeAt (K1.firstJob (X := X) S Zp G).P Ad.msg)) ∧ ch ≤ 1 ∧
      K1.bookCovers Bk ch ⟨(K1.firstJob (X := X) S Zp G).P.place, 0⟩ (K1.dueR (K1.firstJob (X := X)
      S Zp G).P (K1.firstJob (X := X) S Zp G).ride) = true

/-- **At every member of the plan's list of switch places that fits: a lot with its text, in the
list, for K5's triple at a filling's address.** A premise's form. -/
def PlanSwitchLotForFill
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (N : ℕ)
    (S : Sz)
    (G : Ground)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (Ad : MsgAddr)
    (l m' : ℕ) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, ∀ m, Ad = p.ownAddr m → l = p.link → ∃ (D₀ : Pub → Ground →
      RowDataOf ProofFile.Inst) (closing : K2.Closing) (fx ch : ℕ), (⟨P5J.At.num Zp l m', fx,
            K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p (1 + p.sizes.kept.length + m)⟩ :
            MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml ∧ LotsAgree ml ⟨P5J.At.num Zp l m', fx,
                  K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p (1 + p.sizes.kept.length + m)⟩ ∧
      1 + p.sizes.kept.length + m < (K2.switchSent p.sizes p.others).size ∧ 1 + p.sizes.kept.length
      + m ≠ (K2.switchSent p.sizes p.others).size - 1 ∧ ((K2.switchSent p.sizes p.others).getD (1 +
      p.sizes.kept.length + m) default).shape.maskRows ≠ 0 ∧ (∀ row place, (firstData S
      h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K2.switchSeat Zp G) fun _ => 0).lays (p.ownAddr
      m) row place = true → row < ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length +
      m) default).shape.mainRows ∧ place < (p.sizes.codes.base.getD ((K2.switchSent p.sizes
      p.others).getD (1 + p.sizes.kept.length + m) default).shape.code default).ell) ∧ ∀ (k : Coins
      Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place, fillAnswers S
      h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m)
      l m' 0 mask row place = true → (K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
      (1 + p.sizes.kept.length + m) k w (hd.take fx) mask row place).isSome = true

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

