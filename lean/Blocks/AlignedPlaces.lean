-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/AlignedPlaces.lean: a sum over an enumeration is the sum over the type (`sum_toList`).
(Words of this library: lean/GLOSSARY.md.)
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.FinEnum
import Blocks.LevelDef
import Iop.InteractiveOracleProof

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
namespace Places

/-! ## Sums -/

section Keys

variable {V : Type} [DecidableEq V] [FinEnum V]

/-- a sum over the enumeration is the sum over the type -/
theorem sum_toList [Fintype V] (g : V → ℕ) : ((FinEnum.toList V).map g).sum = ∑ v, g v := by
  rw [← List.sum_toFinset g FinEnum.nodup_toList]
  exact Finset.sum_congr (Finset.ext fun v => by simp) fun _ _ => rfl

end Keys

end Places

end Blocks
