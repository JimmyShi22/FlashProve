-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnRun.lean: `RunPlays` at the last chain's own test, at a stand of a thread at border 2: no tree of this chain is
sent in front of it, and each old opening finds a table at hand of the declared width.

  `run_own`: from `agree` and the one premise `hold`.

What stays open. `hold`: every taken opening is at hand, at the width that the round declares: the widths of the tables of
the two earlier chains. `agree`: `agree_at_W`.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.Thread.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **`RunPlays` at border 2.** -/
theorem run_own (T : Thread Bk S Cl V W X Pb) (J : TestJob W X) {k : Coins Bk} {st : S} {m : Mid W X} {E : Env}
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) (hT : Thr T 2 k st m E)
    (ht : treesTo T.bs 2 = 0)
    (hag : Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1))
    (hold : ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc 0 o.2 = true →
      o.2 ∈ T.hand 2 ∧ (T.tableAt o.2 k m).2.words = o.1.W) :
    RunPlays J 0 m E c := by
  have hs : E.sent = 0 := (hT.2.2.2.2.1.2.2.1).trans ht
  refine ⟨hag, hs, fun d hd o ho hold' => ?_⟩
  rw [hs] at hold'
  obtain ⟨hσ, hw⟩ := hold d hd o ho hold'
  obtain ⟨pt, hE, -, hsame⟩ := T.handAt_elim (hT.1.2 o.2 hσ)
  refine ⟨pt, hE, ?_⟩
  unfold Table.same at hsame
  simp only [Bool.and_eq_true, beq_iff_eq] at hsame
  exact hsame.1.2.trans hw

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.run_own
