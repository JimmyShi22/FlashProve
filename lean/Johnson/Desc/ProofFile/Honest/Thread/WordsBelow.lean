-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/WordsBelow.lean: EVERY FIELD ELEMENT THAT THE CHAIN HAS SHOWN
IS BELOW THE PRIME: FROM THE PAIR, NOT FROM THE THREAD ALONE. The thread's own clauses read of the
rounds seen only what was drawn and that the bare fold returns: a stand at which a sent word is
replaced by the same residue above the prime may meet them all: so the sentence is not to be had
from `Thr` (found by a reader of the authors of the kind K13's lemmas). It is what the filling
`SaidOk` of the letter `Said` says of the rounds (Honest/Thread/SaidOk.lean; `saidNext_ok` carries
it past every member of every thread, so it costs no group of authors anything); of the columns it
follows from the tables at hand. Both halves stand inside `reach_below`'s proof; here as a lemma of
their own, in the library's own test `viewWordsBelowPrime` on a view. General in the thread; then at the first
chain's laid letters. No definition. Two conditional lemmas.

  `words_below`        from the pair at `SaidOk`: viewWordsBelowPrime of the chain's rounds seen and its columns
  `head_words_below`   the same at `lettersHead`: no premise beside the pair

Limits. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

/-- **FROM THE PAIR AT `SaidOk`.** hst: the one premise on a letter: the stored tables' words. -/
theorem words_below {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat}
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (hst : ∀ w i x u, T.stored w i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (h : ThrS T SaidOk b k s m E) :
    ∀ cols, T.colsTo b m E = .ok cols → viewWordsBelowPrime ⟨m.seen.drop T.front, cols⟩ = true := by
  intro cols hcols
  obtain ⟨hT, hS⟩ := h
  unfold Thr Thread.Hand at hT
  obtain ⟨⟨hsto, -⟩, -, -, -, -, -, -⟩ := hT
  have hE : ∀ i x u, E.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord := fun i x u hu => by
    rw [hsto i x] at hu
    exact hst _ i x u hu
  unfold Thread.colsTo at hcols
  have hc := fillCols_words _ _ _ (readsOf_words T.chain T.ft E.stored E.tree hE _ _)
    (fun x hx => by cases hx) hcols
  exact (okViewW_split _ _).2 ⟨okRounds_sub hS fun x hx => List.mem_of_mem_drop hx, hc⟩

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT THE FIRST CHAIN's LAID LETTERS**: no premise beside the pair. -/
theorem head_words_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m
      E) :
    ∀ cols, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.colsTo b m E =
        .ok cols →
      viewWordsBelowPrime ⟨m.seen.drop (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front,
                    cols⟩ = true :=
  words_below (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (fun v i p u hu => storedWords_lt H v.w₀ v.rc i p u hu) hT

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.words_below
#print axioms ProofFile.Honest.FirstThread.head_words_below
