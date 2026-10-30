-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ClaimTrueStatement.lean: "THE CLAIM IS TRUE"
(`K11ClaimTrue`, ScriptStatement.lean of this folder) AT THE FIRST CHAIN's THREAD AT THE LIBRARY's
HEAD, OUT OF THE ITEM THAT THE MERGE's MEMBER CLOSES (.forms 24 4 "weights"), FROM THREE PREMISES:
that item is open at border 346; and two facts on the Script's cells: STATEMENTS ALONE: three
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals:
they are lemmas' statements.

  `WaSeatAtHead`        at every stand of the pair `ThrS` at 346 at `SaidOk`: the library's
                        condition on the state in front of the merge, with its eighth clause
                        (`WaSeat`, Johnson/Top/H0/MergeLaw/WtJoinsSeat.lean), at the head's own
                        letters: what the output head's rounds left (`WaK6`), and that the state
                        holds the mask row's seat (`MaskSeatAt`)
  `WeightsItemAtHead`   where the item is open at 346: at every stand of the pair, at the thread's
                        witness at every continuation: the output head's sentence for "weights"
                        (`wtK6`, Johnson/Desc/Kinds/Law/WtK6.lean), at the head's own letters
  `ClaimTrueAtHead`     the base Bs · the item is open at 346 · AT EVERY INPUT OF WHICH Vd HOLDS:
                        the Script's cells hold an index · inside the layout they are the prover's
                        weights' entries:
                        `K11ClaimTrue` at toW := id, Dof := `dataAtHead` (SeatFieldsStatement.lean
                        of this folder), seg := 24

Limits. THE CLAIM's TRUTH IS TAKEN OUT OF THE THREAD's SENTENCE, NOT MADE HERE: the item is opened
by another kind's member: whoever shows the pair at 346 has shown that item. THREE PREMISES STAY IN
THE LAST: THAT THE ITEM IS OPEN AT 346 IS A CLOSED FACT ON WRITTEN LISTS, NOT SHOWN HERE (the
frame's authors list it among the items open there by an evaluation: no theorem); THE TWO ON THE
SCRIPT's CELLS ARE FACTS ON A FREE LETTER: no Script is laid anywhere: whoever lays it pays them.
THAT THE PAIR HOLDS AT ANY STAND IS NOT SAID. THE LAST RESTS ON ANOTHER TEAM's FILE
(`forms_of_wtK6`, Johnson/Desc/Kinds/Law/WtBack.lean) AND IS NO BETTER THAN IT: the
reference sizes alone: at every smaller size its theorems are empty. The head is a premise, at the
earlier hash, at the full size: no example of it is shown here. Nothing on any property.


-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ScriptStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatFieldsStatement
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Top.H0.MergeLaw.WtJoinsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Law (cellAtNo)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaSeat wtK6)
open VerifiableInference.OnPublicFiles.Flat (InRange)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the state in front of the merge. Not proved here; a lemma's statement, none of
the library's goals. -/
def WaSeatAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    WaSeat h.𝔇.arr h.𝔇.N (P5J.At.X Zp) (P5J.At.num Zp 24 0) 0 (P5J.At.X Zp).P.h.V s

/-- The statement on the item. Not proved here; a lemma's statement, none of the library's goals.
-/
def WeightsItemAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
    Item.forms 24 4 "weights" ∈
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 346 →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    ∀ ds, wtK6 h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.X Zp) h.𝔇.layout (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 24 (m.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      (Q.wit k m.st.input (m.st.heard ++ ds))

/-- The statement that the claim is true. Not proved here; a lemma's statement, none of the
library's goals. -/
def ClaimTrueAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (weights : W₀ → Weights),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Item.forms 24 4 "weights" ∈
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 346 →
    (∀ v, Vd v → InRange (Q.cells v)) →
    (∀ v, Vd v → ∀ r c, r < (_root_.K11.parOf Zp Bs.G₀).lay.m0 →
      c < 2 ^ (_root_.K11.parOf Zp Bs.G₀).lay.lk →
      cellAtNo (Q.cells v) r c = Reading.gl.val (eOfF ((weights v.w₀).entry r c))) →
    K11ClaimTrue (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (_root_.K11.parOf Zp Bs.G₀) weights id (dataAtHead h Q carryX) 24

end ProofFile.Honest.K11
