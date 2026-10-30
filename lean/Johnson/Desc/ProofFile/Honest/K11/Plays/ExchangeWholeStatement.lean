-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ExchangeWholeStatement.lean: THE FRAME's DEBT `ExchangeS` AT
NUMBER 346, WHOLE, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD: THE JOIN OF ITS FIVE SHARES:
STATEMENTS ALONE: four definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one
of the library's goals: they are lemmas' statements.

  `OwesAt346`        on the written lists alone: every item that the forward row number 346 owes is
                     one of five: forms 24 9 "merged" · wo 24 · pinW · pin 24 0 · pinI
  `PinsOpenAt346`    on the written lists alone: pin 24 0 and pinI are open at 346
  `ExchangeSOfFive`  at the head's thread, at every Said: the five shares (`ExchangeAtS` at each of
                     the five items) give `ExchangeS` at 346
  `ExchangeSAtHead`  `ExchangeS` at `SaidOk` at 346 FROM: the five premises of `ExchangeAtHead`
                     (SeatedAtHeadStatement.lean of this folder: the kind's own two items) · the
                     thread's keeps at 346 gives `K11Keeps` · `BehindS` at 346 (these two for the
                     frame's authors' `k11_pins_again`, Honest/Thread/K11PinRides.lean: the two
                     pins). The share at pinW asks nothing (their `exchangeAt_pinW`,
                     Honest/Thread/HeadPinW.lean)

Limits. A JOIN: EVERY PREMISE OF THE SHARES STAYS. `BehindS` at 346 is another of the five debts: it
is taken as it stands. The end is a premise's form: THAT THE PAIR `ThrS` HOLDS AT ANY STAND IS NOT
SAID. NO SCRIPT IS LAID IN ANY FILE THAT THE WRITER KNOWS. The head is a premise, at the earlier
hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatedAtHeadStatement
import Johnson.Desc.ProofFile.Honest.Thread.K11PinRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps)
open ProofFile.Honest.SumLaw (SumCoins)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on what the row owes. Not proved here; a lemma's statement, none of the library's
goals. -/
def OwesAt346 : Prop :=
  ∀ i ∈ (FirstRows.rows P5J.At.links P5J.At.ps 346).owes,
    i ∈ [Item.forms 24 9 "merged", Item.wo 24, Item.pinW, Item.pin 24 0, Item.pinI]

/-- The statement on the two pins. Not proved here; a lemma's statement, none of the library's
goals. -/
def PinsOpenAt346 : Prop :=
  Item.pin 24 0 ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 346 ∧
    Item.pinI ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 346

/-- The statement from the five shares. Not proved here; a lemma's statement, none of the library's
goals. -/
def ExchangeSOfFive : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop),
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346
      (Item.forms 24 9 "merged") →
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346
      (Item.wo 24) →
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346
      Item.pinW →
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346
      (Item.pin 24 0) →
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346
      Item.pinI →
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346

/-- The statement at the head. Not proved here; a lemma's statement, none of the library's goals.
-/
def ExchangeSAtHead : Prop :=
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
      K11Keeps (_root_.K11.parOf Zp Bs.G₀) s s') →
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 →
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346

end ProofFile.Honest.K11
