-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Opens.lean: bounds on the number of elements of unions and images of finite sets.

`Opens.cardU`: a union of two sets; `Opens.cardI`: an image; `Opens.cardB`: a union over a finite
set; `Opens.card_univ_fin`: `Fin n` has at most n elements.
-/
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option linter.unusedSectionVars false

namespace Blocks
open Iop

/-! Cardinalities of unions and images, with the decision procedure for equality taken from the
goal. -/

namespace Opens

theorem cardU {α : Type} {d : DecidableEq α} (s t : Finset α) {a b : ℕ}
    (hs : s.card ≤ a) (ht : t.card ≤ b) : (s ∪ t).card ≤ a + b :=
  le_trans (Finset.card_union_le _ _) (Nat.add_le_add hs ht)
theorem cardI {α β : Type} {d : DecidableEq β} (f : α → β) (s : Finset α)
    {a : ℕ} (hs : s.card ≤ a) : (s.image f).card ≤ a :=
  le_trans Finset.card_image_le hs
theorem cardB {α β : Type} {d : DecidableEq β} (s : Finset α) (t : α → Finset β)
    (a : α → ℕ) (h : ∀ x ∈ s, (t x).card ≤ a x) :
    (s.biUnion t).card ≤ ∑ x ∈ s, a x :=
  le_trans Finset.card_biUnion_le (Finset.sum_le_sum h)
theorem card_univ_fin (n : ℕ) : (Finset.univ : Finset (Fin n)).card ≤ n := by simp

end Opens
open Opens

end Blocks
