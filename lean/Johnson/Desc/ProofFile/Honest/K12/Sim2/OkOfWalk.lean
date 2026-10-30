-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the words that a walked stand has seen are below the prime.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/OkOfWalk.lean: the step from the letter SaidOk to the letter
SaidWalk (Thread/WalkedTo.lean), which the first chain's said₁ of TheLetters is: where the first stand
has seen only words below the prime, so has every stand walked to from it. So hSaid of
onAtRun_at_maker_thread (LeftAtL.lean), at said₁: each stand of SaidWalk holds SaidOk.

  walkedTo_ok, saidWalk_ok   the statements

No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.WalkedTo
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (viewWordsBelowPrime)
open ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A walked stand has seen words below the prime.** -/
theorem walkedTo_ok (T : Thread Bk S Cl V W X Pb) {m₀ : Coins Bk → Mid W X} {k : Coins Bk}
    (h0 : viewWordsBelowPrime ⟨(m₀ k).seen, []⟩ = true) {b : Nat} {m : Mid W X} (h : WalkedTo T m₀ k b m) :
    viewWordsBelowPrime ⟨m.seen, []⟩ = true := by
  induction h with
  | start => exact h0
  | next =>
    rename_i ih
    obtain ⟨⟨l, hl, hy⟩, -⟩ := ‹T.Moved _ _ _ _ _ _ _›
    have hdl := steps_decl hl
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hdl
    have h1 := okViewW_of_yields _ _ _ _ (play_yields _ _ _ _ _ hy)
      (by rw [hdl]; exact drawsFit_bare _ _ (by assumption)) okViewW_nil
    have g := (okRounds_append _ _).2 ⟨ih, h1⟩
    rw [← (play_mid _ _ _ _ _ hy).2.2] at g
    exact g

/-- **The letter SaidWalk holds SaidOk**, at a first stand that has seen nothing. -/
theorem saidWalk_ok (T : Thread Bk S Cl V W X Pb) {B : Coins Bk → Mid W X → List VerifiableInference.Desc.OpenedColumn → Prop}
    {m₀ : Coins Bk → Mid W X} (h0 : ∀ k, (m₀ k).seen = []) (b : Nat) (k : Coins Bk) (m : Mid W X)
    (h : SaidWalk T B m₀ b k m) : SaidOk b k m :=
  walkedTo_ok T (by rw [h0]; exact okViewW_nil) h.2

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.walkedTo_ok
#print axioms ProofFile.Honest.K12.Sim2.saidWalk_ok
