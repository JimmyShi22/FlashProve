-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatPaired.lean.

What is here. The library's tape of a view's rounds (`paired`, OnBytes/K/Kc/Laws.lean), from its
round number k on, holds what a stretch of these rounds from number k on holds (`TapeIs`,
FlatCore.lean). Statements and proofs.

  `tapeIs_paired`   from the rounds' numbers
  `tapeIs_paired_drop`   for the stretch of n rounds from number k on

Limits. A word on lists alone: which rounds a part has played, and at which number they begin, is
the caller's. It stands on `paired_sent` and `paired_drawn` of RowKit.lean beside this file. No
property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatCore
import Johnson.Desc.ProofFile.Honest.K4.Law.RowKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.K.Kc (paired)

/-- The tape from round number k on holds what the rounds hold that stand from number k on. -/
theorem tapeIs_paired (rs : List Fmt.RoundView) (es : List Fmt.Entry) (k : ℕ) (rounds : List Fmt.RoundView)
    (h : ∀ (n : ℕ) (r : Fmt.RoundView), rounds[n]? = some r → rs[k + n]? = some r) :
    TapeIs ((paired rs es).drop k) rounds := by
  intro n r hn
  rw [List.drop_drop, paired_sent, paired_drawn, h n r hn]
  exact ⟨rfl, rfl⟩

/-- The stretch of n rounds from number k on. -/
theorem tapeIs_paired_drop (rs : List Fmt.RoundView) (es : List Fmt.Entry) (k n : ℕ) :
    TapeIs ((paired rs es).drop k) ((rs.drop k).take n) := by
  refine tapeIs_paired rs es k _ fun i r hi => ?_
  rw [List.getElem?_take] at hi
  split at hi
  · rw [List.getElem?_drop] at hi
    exact hi
  · cases hi

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tapeIs_paired
#print axioms ProofFile.Honest.K4.tapeIs_paired_drop
