-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/DebtsKit.lean: TWO GENERAL LEMMAS ON WHAT A CHAIN's THREAD ASKS AT
A MEMBER (Honest/Thread/Pays.lean): on the frame's `chainSteps` at a list of one member, and on the
thread's `fresh`. No kind is named. Statements with their proofs.
Main names:
  `chainSteps_one`: what `chainSteps` lays for one member at whose place a half stands: the book
    lends the row its coins, and the steps are the half's.
  `fresh_none`: a member that states no oracle message brings no new tree.

What is not claimed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Block)

/-- **What `chainSteps` lays for one member at whose place a half stands**: where it returns, the
book has lent the row its coins c, and the steps are the half's at c. -/
theorem chainSteps_one {St Cl V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {b : Block St Cl} {hs : List (Placed V W X)}
    {h : Placed V W X} {l : List (Step W X)}
    (hf : (hs.find? fun h => h.place == b.place) = some h)
    (hl : chainSteps B rows look v [b] hs = .ok l) :
    ∃ c, lendRow B rows look b.place h.parts 0 = .ok c ∧ l = h.steps b v c := by
  simp only [chainSteps, hf] at hl
  split at hl
  · cases hl
  split at hl
  · cases hl
  split at hl
  · cases hl
  split at hl
  · cases hl
  split at hl
  · cases hl
  cases hc : lendRow B rows look b.place h.parts 0 with
  | error e =>
    rw [hc] at hl
    cases hl
  | ok c =>
    rw [hc] at hl
    refine ⟨c, rfl, ?_⟩
    have e : (Except.ok (h.steps b v c ++ []) : Except String (List (Step W X))) = .ok l := hl
    rw [List.append_nil] at e
    exact (Except.ok.inj e).symm

/-- A member that states no oracle message brings no new tree. General in the thread. -/
theorem fresh_none {Bk : ProverCoinCounts} {T₀ C V W Y Q : Type}
    (T : Thread Bk T₀ C V W Y Q) {b : Nat} {blk : Block T₀ C}
    (hb : T.bs[b]? = some blk) (ho : blk.oracles.flatMap id = []) : T.fresh b = [] := by
  have e : T.hand (b + 1) = T.hand b := by
    unfold Thread.hand
    rw [treesTo_succ hb, ho]
    rfl
  unfold Thread.fresh
  rw [e, List.filter_eq_nil_iff]
  intro σ hσ
  simp [hσ]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.chainSteps_one
#print axioms ProofFile.Honest.K13.fresh_none
