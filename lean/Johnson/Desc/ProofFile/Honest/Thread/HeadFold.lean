-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadFold.lean: at the first chain's invariant at the full size
(`lettersHead`, FirstHead.lean), the state at a border is what the library's `foldBlocks` returns
over the sub-protocols before that border, from the chain's first state `ProofFile.startS Zp` at the
instance's public part, at the rounds that the run has shown and at the columns that these
sub-protocols read. It is read off the part `Made` of the invariant `Thr` (Thr.lean). At the last
border the fold is over the chain's whole flat list. Lemmas of other authors on the last chain's
start have that equation as a hypothesis. No definition.

  1  `head_fold_at`   at every border
  2  `head_fold_end`   at the last border

Limits.
  * That the invariant holds at any run is not shown.
  * How the state at the first chain's last border is handed to the later chains is not treated.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place foldBlocks)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The state at a border is the fold's return over the sub-protocols before it. -/
theorem head_fold_at {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    ∃ cols, foldBlocks 0 (cF.blocksInOrder.take b) (ProofFile.startS Zp m.st.input.x.pub) m.seen cols =
      .ok (s, [], []) := by
  obtain ⟨-, -, -, -, s₀, cols, hb, -, hf⟩ := hT.2.2.2.2.1
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  have hf' : foldBlocks 0 (cF.blocksInOrder.take b) s₀ (m.seen.drop 0) cols = .ok (s, [], []) := hf
  rw [List.drop_zero, hb'] at hf'
  exact ⟨cols, hf'⟩

/-- At the last border the fold is over the chain's whole flat list. -/
theorem head_fold_end {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread cF.blocksInOrder.length k s m
      E) :
    ∃ cols, foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp m.st.input.x.pub) m.seen cols =
      .ok (s, [], []) := by
  obtain ⟨cols, hf⟩ := head_fold_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT
  rw [List.take_length] at hf
  exact ⟨cols, hf⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_fold_at
#print axioms ProofFile.Honest.FirstThread.head_fold_end
