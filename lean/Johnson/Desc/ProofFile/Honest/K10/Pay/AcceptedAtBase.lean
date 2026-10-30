-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/AcceptedAtBase.lean: the closing of a segment (K10) at the prover that the maker
`onlineProverFromPublicFiles` returns at the filling `onlineProverPartsInUse I o S O` itself, not read through: the search at each closing's place
finds the closing's own half, and the forms `PlaysS` and `AcceptedS` (Honest/Thread/PaysS.lean) hold at all 25 closings of
the first chain's thread under the library's head at that prover. The index's reader I is a letter.

  `wLotAt_not_K10`       no half of the message W's lot stands at a place of the kind K10
  **`closingsFirst_base`**   where `onlineProverFromPublicFiles` returns A at that filling: the returned description opens at some first chain c, and
                       `ClosingsFirst` (Honest/K10/Thr/HalfOfLot.lean) holds of A's list for the first chain
  `closingsFirst_baseHead`   under the head: A's public part is the head's, and `ClosingsFirst` at the head's public part and
                       first chain
  **`playsS_base`**, **`acceptedS_base`**   the two forms at each closing's border, at A's prover

  `playsS_baseAt`, `acceptedS_baseAt`   the same at any prover whose list for the first chain is A's: its stored tables and its
                       key are free

Limits. The head and the return of `onlineProverFromPublicFiles` are premises; the thread's further parameters are letters. `closingsFirst_base`
says nothing where the public part has no closing (`closePars` is empty); under the head there are 25. Where the thread's
invariant holds at no stand of a border both forms hold there for nothing. They do not say what the part sends.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.Accepted
import Johnson.Desc.ProofFile.Honest.K10.Pay.ClosingsAtFill
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Kinds
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Place Strs KindName)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {W₀ : Type}

/-- No half of the message W's lot stands at a place of the kind K10. -/
theorem wLotAt_not_K10 {X : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ e ∈ (wLotAt (X := X) I o O).halves Z G, e.place.kind ≠ KindName.K10 := by
  intro e he
  rw [wLotAt_halves] at he
  cases hm : OnBytes.linMessageW Z.first.lin with
  | none =>
    rw [hm] at he
    cases he
  | some msg =>
    rw [hm] at he
    rcases List.mem_singleton.1 he with rfl
    intro hk
    cases hk

/-- **At the filling itself each closing's place is served by the closing's own half.** -/
theorem closingsFirst_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    ∃ Bs base c Sh Se, IM.Open o' pol lay KL A.F A.Z Bs base c Sh Se ∧
      ClosingsFirst A.H.first (fun w : Local W₀ IndexCommitterCoins Inst Cells => (⟨w.trace, I.weights A.Z w.w₀, w.rc⟩ : Readers))
        (widerRows S A.Z A.G) (stAtZero c.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G := by
  obtain ⟨Bs, base, c, Sh, Se, Op⟩ := atPure_open hA
  refine ⟨Bs, base, c, Sh, Se, Op, ?_⟩
  refine closingsFirst_of_fill hA _ _ _ (Lc := closeLotAt I S) ?_ (closeLotAt_of_open (X := Unit) I S A.G Op) ?_
  · rw [widerFillAtCPUOWM_lots]
    simp
  · intro M hM
    rw [widerFillAtCPUOWM_lots] at hM
    simp only [List.mem_append, List.mem_singleton] at hM
    rcases hM with ((h | rfl) | rfl) | rfl
    · exact .inl (ten_not_K10_plain I o S O A.Z A.G M h)
    · exact .inr rfl
    · refine .inl fun e he hk => ?_
      have hk' := proxLotAt_kinds I S A.Z A.G e he
      rw [hk] at hk'
      cases hk'
    · exact .inl (wLotAt_not_K10 I o O A.Z A.G)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head: the returned public part is the head's, and the premise holds at the head's public part and chain. -/
theorem closingsFirst_baseHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A) :
    A.Z = Zp ∧ ClosingsFirst A.H.first
      (fun w : Local W₀ IndexCommitterCoins Inst Cells => (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers))
      (widerRows S Zp A.G) (stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Zp ξ.pub) Zp A.G := by
  obtain ⟨Bs, base, c, Sh, Se, Op, hC⟩ := closingsFirst_base I o S O hA
  have eZ : A.Z = Zp := Except.ok.inj ((atPure_ok hA).1.symm.trans h.laid.pub)
  obtain ⟨Bs', base', O'⟩ := h.laid.opened
  have e1 := ToldDesc.pureChainAt_of_open Op
  have e2 := ToldDesc.pureChainAt_of_open O'
  rw [eZ] at e1
  obtain rfl : c = cF := Except.ok.inj (e1.symm.trans e2)
  rw [eZ] at hC
  exact ⟨eZ, hC⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
  (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A) {Bk : ProverCoinCounts}
  (Sc : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

include hA in
/-- **At that prover the closing's part plays at each of the 25 closings**, at every Said. -/
theorem playsS_base (l : Nat) (hl : l < 25)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    PlaysS (lettersHead h A.H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (14 * l + IM.nAt l + 5) :=
  playsS_at_head h A.H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl rfl _ _ _ A.G
    (closingsFirst_baseHead h I o S O hA).2 Said

include hA in
/-- **At that prover the closing's block accepts at each of the 25 closings**, at every fall and at every Said that gives
`SaidOk`. -/
theorem acceptedS_base (l : Nat) (hl : l < 25)
    {Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h A.H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
      (14 * l + IM.nAt l + 5) :=
  acceptedS_at_closing h A.H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl _ _ _ A.G
    (closingsFirst_baseHead h I o S O hA).2 hSaid fall

/-! ## At any prover with that list for the first chain -/

section
variable {Ky X₀ : Type} (H' : Prover W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit) (e : H'.first = A.H.first)

include hA e in
/-- The closing's part plays at each closing, at any prover whose list for the first chain is A's: its other fields (the
stored tables, the key) are free. -/
theorem playsS_baseAt (l : Nat) (hl : l < 25)
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    PlaysS (lettersHead h H' Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (14 * l + IM.nAt l + 5) :=
  playsS_at_head h H' Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl rfl _ _ _ A.G
    (e ▸ (closingsFirst_baseHead h I o S O hA).2) Said

include hA e in
/-- The closing's block accepts at each closing, at any such prover. -/
theorem acceptedS_baseAt (l : Nat) (hl : l < 25)
    {Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H' Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
      (14 * l + IM.nAt l + 5) :=
  acceptedS_at_closing h H' Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl _ _ _ A.G
    (e ▸ (closingsFirst_baseHead h I o S O hA).2) hSaid fall

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.wLotAt_not_K10
#print axioms ProofFile.Honest.K10.playsS_baseAt
#print axioms ProofFile.Honest.K10.acceptedS_baseAt
#print axioms ProofFile.Honest.K10.closingsFirst_base
#print axioms ProofFile.Honest.K10.closingsFirst_baseHead
#print axioms ProofFile.Honest.K10.playsS_base
#print axioms ProofFile.Honest.K10.acceptedS_base
