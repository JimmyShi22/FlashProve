-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PileAtHead.lean: THE PILE's LENGTH IS A FACT AT REACHED STATES
TOO: SO NEITHER OF THE TWO COUNTING CLAUSES OF `rides` IS NEEDED. `riderPile`
(Honest/Thread/Riders.lean) was laid as a clause of the first chain's letter `rides`: the pile of
pending rows has as many rows as links that leave a row are cleared in front of the border.
The kind K13's lemmas show it at every state that is
reached by the members' own steps, up to border 355, under what the library's head holds:
`pile_length_reach` (Honest/K13/PileLengthReach.lean), at the library's own count `P1L20.takenAt`.
The thread gives that reach (`thr_reach`). With `head_roomLeft` (Honest/Thread/RoomAtHead.lean) the
counting clause's sentence on the index masks' ledger follows from the thread and one public
inequality. Calls.

  `head_pile`         the pile's length, wherever the thread holds, up to border 355
  `head_pile_355`     thirteen rows in front of the batching of the pending rows
  `head_roomLeft_thr` `RoomLeft` and "a member of no group" from the thread and the inequality

Limits. The full size and the format's second hash function alone. The library's head has a member at the
name under four premises on the public files (the seal's `head_exists_at_name`); none of our files
calls it; no member of the head together with the thread's sentence is shown. It stands over three
files of these authors, which are in the sealed library. The inequality (the plan's room is at most
the fresh ledger's free count) stays a premise on public data. None is one of the library's goals.
This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RoomAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileLengthReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PILE's LENGTH, WHEREVER THE THREAD HOLDS, UP TO BORDER 355.** -/
theorem head_pile (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length) (h355 : b ≤ 355)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    s.out.pending.length = P1L20.takenAt b := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  exact (ProofFile.Honest.K13.pile_length_reach h.scope h.reads O h.toAtMg.laid.planOk
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT) h355).2

/-- Thirteen rows in front of the batching of the pending rows. -/
theorem head_pile_355 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : 355 ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 355 k s m E) :
    s.out.pending.length = 13 := by
  rw [head_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb (Nat.le_refl 355) hT]
  exact ProofFile.Honest.K13.takenAt_355

/-- **THE COUNTING CLAUSE's OWN SENTENCE, FROM THE THREAD AND ONE INEQUALITY ON PUBLIC DATA.** -/
theorem head_roomLeft_thr (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {room : Nat}
    (hle : ∀ Bs base, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs
      base cF (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      room ≤ VerifiableInference.Desc.K1.free0Of Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp))
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h355 : b ≤ 355)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    RoomLeft room s ∧ P1L20.outOfGroupsB s = true :=
  head_roomLeft h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hle hb h3 h355 hT
    (head_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb h355 hT)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_pile
#print axioms ProofFile.Honest.FirstThread.head_pile_355
#print axioms ProofFile.Honest.FirstThread.head_roomLeft_thr
