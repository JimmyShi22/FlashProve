-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersLean.lean: conditional: the opening's form of the attention
sub-protocol's premise on the senders' lots. One definition, one theorem.

  OpeningLotForFillLean              OpeningLotForFill (SendersPlan.lean in this folder) without two of its
                                     clauses. A premise's form; a type and a letter of the sender's job
                                     stand under "there is"
  covers_of_openingLotForFillLean    it gives the covering of the filling's lot at segment 0

What the form keeps: the lot stands in the list, LotsAgree, ch ≤ 1, hBk. hBk (K1.bookCovers) says that the book covers what
is due, not that it equals it, and is run at no book. The opening's form stands in two texts, this one and
SendersPlan's, held together by nothing.

The premises of the theorem: h, the library's head; hG; the typed seat's equation; H, the form itself.

Limits.
  * Conditional. This file proves none of its premises of any list, reader, book, instance or filling.
  * The reader rd is a letter. The index type W₀ is a letter.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, the first chain alone, at the
    earlier hash OnBytes.secondHashFunction, a fixed function.
  * Through its imports it stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersTests
import Johnson.Desc.ProofFile.Honest.K5.Law.FillOpeningHead
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsSendersNine
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceAtFullIn
import Johnson.Desc.ProofFile.Honest.K5.Law.Eight
import Johnson.Flat.ThreeFull
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput

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
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)

variable {W₀ : Type} {wt : W₀ → Weights} {cellsOf : W₀ → P5J.CellsM OnBytes.Flat.numsFull}

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **`OpeningLotForFill` without its clauses ha and hIn.** A premise's form. A type and a letter of
the sender's job stand under "there is". -/
def OpeningLotForFillLean
    (Zp : ProofFile.Pub)
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (S : Sz)
    (G : Ground)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (Ad : MsgAddr)
    (m' : ℕ) :
    Prop := ∃ (X : Type) (own₀ : X) (fx ch : ℕ), (⟨P5J.At.num Zp 0 m', fx, K1.msgTxt ch rd
      (K1.firstJob (X := X) S Zp G) own₀ Ad.msg⟩ : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml ∧
      LotsAgree ml ⟨P5J.At.num Zp 0 m', fx, K1.msgTxt ch rd (K1.firstJob (X := X) S Zp G) own₀
      Ad.msg⟩ ∧ ch ≤ 1 ∧ K1.bookCovers Bk ch ⟨(K1.firstJob (X := X) S Zp G).P.place, 0⟩ (K1.dueR
      (K1.firstJob (X := X) S Zp G).P (K1.firstJob (X := X) S Zp G).ride) = true

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **The leaner form gives the clause of SF0 at segment 0.** CONDITIONAL: under the
hypothesis h; hG; the typed seat's equation. -/
theorem covers_of_openingLotForFillLean
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {S : Sz}
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G)
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {Ad : MsgAddr}
    {m' : ℕ}
    (hAd : typedSeat h G 0 Ad = some (0, m'))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (N : ℕ)
    (H : OpeningLotForFillLean Zp ml S G rd Ad m') :
    ∃ Ls ∈ ml, LotsAgree ml Ls ∧ Covers Vd N Ls (fillLot (Bk := Bk) h S rd (typedSeat h G 0) (fun _
      => 0) Ad 0 m') := by
  obtain ⟨X, own₀, fx, ch, hm, ha', hc, hBk⟩ := H
  have es : typedSeat h G 0 = K1.firstSeat h.𝔇.sent.shape 0 := if_pos rfl
  rw [es] at hAd ⊢
  obtain ⟨s, n⟩ := Ad
  have e1 : s = K1.firstAddr := congrArg MsgAddr.sender (seated_at_opening hAd).1
  subst e1
  exact ⟨_, hm, ha', covers_fill_opening_head h S hG rd own₀ hAd fx ch rfl hc hBk Vd N⟩

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

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.covers_of_openingLotForFillLean
