-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Reads.lean: a bound on the number of elements of a finite set.

`card_le_of_forall_exists`: a finite set all of whose elements are values of a function on ι has at
most |ι| elements.
-/
import Code.Facts
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Blocks

open Iop Prob Finset

/-- A finite set all of whose elements are values of a function on ι has at most |ι| elements. -/
theorem card_le_of_forall_exists
    {α ι : Type} [Fintype ι] (s : Finset α) (f : ι → α) (h : ∀ p ∈ s, ∃ i, p = f i) :
    s.card ≤ Fintype.card ι := by
  classical
  refine (card_le_card (t := univ.image f) fun p hp => ?_).trans card_image_le
  obtain ⟨i, rfl⟩ := h p hp
  exact mem_image_of_mem f (mem_univ i)

end Blocks
