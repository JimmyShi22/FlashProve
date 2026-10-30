-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FiveAtHeadStatement.lean: ALL FIVE OF THE FRAME's DEBTS AT
NUMBER 346 (`PlaysS`, `AcceptedS`, `BehindS`, `ExchangeS`, `RidesPastS`; Honest/Thread/PaysS.lean),
AT `SaidOk`, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD, IN ONE SENTENCE, WITH ALL THAT THEY
TAKE WRITTEN OUT ONCE: A STATEMENT ALONE: one definition of a proposition. NOTHING IS PROVED IN THIS
FILE, and it is none of the library's goals: it is a lemma's statement.

  `FiveAtHead`  the five, FROM ELEVEN PREMISES BESIDE THE HEAD:
                 (1) the maker's base · (2) b₀ ≤ 346
                 (3) the prover's half at the merge's place is the kind's, at the claims
                     `headClaimsAt cF Zp Bs.G₀`
                 (4) (5) the facts on the script: `K11ScriptMsg` · `K11CellsQ`
                 (6) the thread's keeps at 346 gives `K11KeepsYes` · (7) `K11KeepsYes` gives the
                     thread's keeps at 346: TOGETHER: keeps at 346 is that clause (the kind's
                     clause, and that the merge's decision has said yes)
                 (8) behind the member's step, with that clause in hand, the letter Rd holds at 347
                 (9) (10) (11) the shares of `RidesPastS` at pile · worth 24 8 "planes" ·
                     worth 24 8 "keys"

Limits. A JOIN OF FIVE LEMMAS: NO PREMISE IS PAID HERE. THAT THE ELEVEN CAN BE MET TOGETHER IS NOT
SHOWN. AT A THREAD WHOSE keeps AT 346 IS THE WEAKER CLAUSE `K11Keeps`, (6) IS NOT TO BE HAD. The
five ends are premises' forms: THAT THE PAIR `ThrS` HOLDS AT ANY STAND IS NOT SAID. NO SCRIPT IS
LAID IN ANY FILE THAT THE WRITER KNOWS. The head is a premise, at the earlier hash, at the full
size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ExchangeWholeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.RidesWholeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.BehindYesAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.PlaysAtHeadStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes)
open ProofFile.Honest.SumLaw (SumCoins)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def FiveAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (weights : W₀ → Weights)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay)),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs → b₀ ≤ 346 →
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find? fun g =>
      g.place == IM.k11Place) =
        some (headMergeHalf (headClaimsAt cF Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀)) →
    K11ScriptMsg (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) weights IM.k11Place c₀)
      id id (dataAtHead h Q carryX) 24 →
    K11CellsQ Q (_root_.K11.parOf Zp Bs.G₀).lay weights Vd →
    (∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s') →
    (∀ s s', K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s') →
    (∀ blk k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      cF.blocksInOrder[346]? = some blk → K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' →
      Rd 347 y.2.st.input s') →
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      Item.pile →
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (Item.worth 24 8 "planes") →
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (Item.worth 24 8 "keys") →
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 ∧
    (∀ fall, AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk fall
      346) ∧
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 ∧
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 ∧
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346

end ProofFile.Honest.K11
