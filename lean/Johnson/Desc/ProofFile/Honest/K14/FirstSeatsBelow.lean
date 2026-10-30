-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/FirstSeatsBelow.lean: at the full size, at every state without a
mark of failure that the first chain's own steps reach: every message that has a seat in the
verifier's book of trees sits in a tree whose number is below the number of trees that the first
chain sends, which is 83. Statements with their proofs; no definition.

What for. A witness of the second chain holds the first chain's messages and, at the seats of trees
from that number on, messages of the shared chain (lastWitness, Honest/Thread/TheFirstThread.lean).
A sentence on the first chain's words is carried to such a witness where the seats that it reads lie
below that number (the premise hs of wordsBy_first, Honest/K14/FirstAtLastWitness.lean).

  trees_below         at a reached state the book holds at most 83 trees
  first_seats_below   **at a reached state: a seat that seatBy noFirst
                      (Johnson/Desc/Sound/TabAt.lean) reads off the book lies in a tree below
                      (F0T …).t₁**
  head_seats_below    the same where the first chain's invariant holds (lettersHead,
                      Honest/Thread/FirstHead.lean), at a border within the chain

From the library's facts on reached states (reach_facts, reach_treeNumber,
Honest/Thread/BookFacts.lean): the book's trees have the shapes of the written layout as far as the
book goes, and no more trees than it (the field seatsCarried); a tree's own number is its place in
the book. The written layout has 83 shapes (laid_sizes, Johnson/HB/LLHARD/LaidWritten.lean), and the
description's first chain sends 83 trees (counts_of_data, Johnson/Desc/Sound/TakenBelowOfData.lean;
AtMg.trees, Johnson/HB/LLHARD/HeadFacts.lean). Kin: first_trees_83 (Honest/K14/ArrAtHead.lean) has
that last sentence under a name; it is proved again here so that this file stands on fewer others.

Limits.
  * THE PREMISE h IS A HYPOTHESIS: P5J.AtMgA (Johnson/P5J/MgAtAll.lean) at the hash OnBytes.secondHashFunction.
    This file does not show it to be met.
  * The first chain's book alone. Where the book has no seat for a message, nothing is said of it:
    at the chain's start the book is empty, and the statements hold for want of a seat.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.BookFacts
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.Sound.TakenBelowOfData
import Johnson.HB.LLHARD.HeadFacts
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT seatBy noFirst)
open VerifiableInference.Desc.K13.Law (LFull laid_sizes)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At a reached state without a mark of failure the book holds at most 83 trees. -/
theorem trees_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat}
    {a : ProofFile.InstPub × TS} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (h0 : a.2.failed = none) :
    a.2.book.trees.size ≤ 83 := by
  have e : VerifiableInference.Desc.K12.Door.seatsCarriedB LFull a.2.book = true :=
    (reach_facts h).seatsCarried b a hR h0
  unfold VerifiableInference.Desc.K12.Door.seatsCarriedB at e
  simp only [Bool.and_eq_true, decide_eq_true_eq] at e
  exact laid_sizes.2.2.1 ▸ e.2

/-- **At a reached state without a mark of failure: a seat that is read off the first chain's book
lies in a tree below the number of trees that the first chain sends.** -/
theorem first_seats_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat}
    {a : ProofFile.InstPub × TS} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (h0 : a.2.failed = none) :
    ∀ o q, seatBy noFirst a.2.book o = some q → q.1 < (F0T OnBytes.secondHashFunction Zp Np cF).t₁ := by
  have e83 : (F0T OnBytes.secondHashFunction Zp Np cF).t₁ = 83 :=
    (VerifiableInference.Desc.counts_of_data h.laid.data).1.symm.trans h.toAtMg.trees.1
  intro o q hq
  unfold seatBy at hq
  obtain ⟨p, -, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hq
  have hn : T.number = p.1 := reach_treeNumber h hR h0 p.1 T hT
  have hl : p.1 < a.2.book.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
  have hb := trees_below h hR h0
  show T.number < _
  rw [e83, hn]
  omega

/-- The same where the first chain's invariant holds, at a border within the chain. -/
theorem head_seats_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    ∀ o q, seatBy noFirst s.book o = some q → q.1 < (F0T OnBytes.secondHashFunction Zp Np cF).t₁ :=
  first_seats_below h (a := (m.st.input.x.pub, s))
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.trees_below
#print axioms ProofFile.Honest.K14.first_seats_below
#print axioms ProofFile.Honest.K14.head_seats_below
