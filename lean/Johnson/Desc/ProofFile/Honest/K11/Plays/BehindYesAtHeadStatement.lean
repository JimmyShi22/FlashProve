-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/BehindYesAtHeadStatement.lean: THE FRAME's DEBT `BehindS` AT
NUMBER 346, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD AND AT `SaidOk`, WHERE THE THREAD's
"keeps" AT 346 IS LAID AT THE KIND's STRONGER CLAUSE `K11KeepsYes`
(Johnson/Desc/K11/Returns/KeepsYesStatement.lean): STATEMENTS ALONE: two definitions of
propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are
lemmas' statements.

  `BehindYesSAtHead`      `BehindSAtHead` (BehindAtHeadStatement.lean of this folder) with
                          `K11KeepsYes` where that has `K11Keeps`, two places
  `BehindYesSAtHeadOfRd`  `BehindSAtHeadOfRd` (BehindOfRdStatement.lean of this folder) with the
                          same turn, two places: the base · b₀ ≤ 346 · the stronger clause gives the
                          thread's keeps at 346 · behind the member's step, with that clause in
                          hand, the letter Rd holds at 347: `BehindS` at 346

Why. The two elder statements take "`K11Keeps` gives keeps". At a thread whose keeps at 346 is laid
at the stronger clause that premise asks that `K11Keeps` give `K11KeepsYes`: WHICH IS NOT SHOWN,
AND WHICH BY READING DOES NOT HOLD (in the weaker clause what the merge leaves for the row on the
weights is a bare "there is": so it allows states behind that no yes of the merge reaches: NO
EXAMPLE IS TYPED). So at that laying the other two have a premise that nobody can be asked to pay;
these take the premise that the laying itself gives. The items "forms" ride past 346 from the
stronger clause alone (SixRideStatement.lean of this folder): so the frame's authors lay that one.

Limits. THE TWO PREMISES ON Kp AND Rd ARE SHOWN AT NO FILLING OF THESE LETTERS. THE ELDER TWO STAND:
a thread laid at the weaker clause still takes them. All the limits of BehindAtHeadStatement.lean
and BehindOfRdStatement.lean. The head is a premise here, at the earlier hash, at the full size.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.BehindOfRdStatement
import Johnson.Desc.K11.Returns.KeepsYesStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement with the rider as a premise. Not proved here; a lemma's statement, none of the
library's goals. -/
def BehindYesSAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ s s', K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s') →
    (∀ blk k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      cF.blocksInOrder[346]? = some blk → K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.rides 347 y.2.st.input
        s') →
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346

/-- The statement with the rider on the reply paid. Not proved here; a lemma's statement, none of
the library's goals. -/
def BehindYesSAtHeadOfRd : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs → b₀ ≤ 346 →
    (∀ s s', K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s') →
    (∀ blk k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      cF.blocksInOrder[346]? = some blk → K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s' →
      Rd 347 y.2.st.input s') →
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346

end ProofFile.Honest.K11
