-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CompleteAcc.lean: a lemma on lists. If no entry stands twice in a list, and whatever passes
the test `φ` is in the finite set `A`, then at most |A| entries of the list pass the test
(`length_filter_le_card`).
-/
import Compile.EraseKit
import Compile.MerkleRom
import Compile.SpecAdaptive
import Mathlib.Data.Finset.Sum

noncomputable section

namespace Compile.Cmpl
open Iop Rom

variable {I X : Type} {lam K : ℕ}

theorem length_filter_le_card {α : Type} (l : List α) (hl : l.Nodup) (φ : α → Bool) (A : Finset α)
    (hA : ∀ a, φ a = true → a ∈ A) : (l.filter φ).length ≤ A.card := by
  classical
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  exact Finset.card_le_card fun a ha => hA a (List.mem_filter.1 (List.mem_toFinset.1 ha)).2

end Compile.Cmpl
