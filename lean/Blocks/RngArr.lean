-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngArr.lean: a sum over the vectors of a protocol that sends none.

`sum_zero_of_all`: if no vector is sent (`EncData.All` at the property `False`,
Blocks/StageSide.lean), every sum over the vectors is 0.
Notation: `EncData.sum f`: the sum of f (code, rows, row variables, role, positions read) over all
vectors of all rounds (Blocks/StageCount.lean).

Terms: lean/GLOSSARY.md.
-/
import Blocks.RngFront
import Blocks.StageOnCore
import Blocks.VecEnum
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.Rng.Par

open Iop Prob

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] (E : Type) [Field E] [NeZero (2 : E)]
    [Fintype E] [DecidableEq E] [Algebra F E]

/-- If no vector is sent, every sum over the vectors is 0. (stated for 2 ≠ 0 in E) -/
theorem sum_zero_of_all {s : Shape} {d : EncData F E s}
    (h : EncData.All (fun _ _ _ _ _ => False) s d) (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) :
    EncData.sum f s d = 0 := by
  rw [← EncData.sum_eq]
  exact Finset.sum_eq_zero fun v _ => (h.apply v).elim

end Blocks.Rng.Par
