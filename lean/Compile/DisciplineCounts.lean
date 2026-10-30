-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DisciplineCounts.lean: of the 2^depth leaves of a tree, those that satisfy f and those that
do not are 2^depth together (`cntLeaves_add`; `cntLeaves`: Compile/SpecDiscipline.lean).
-/
import Compile.SpecDiscipline

namespace Compile.Disc.Counts

open Iop Rom

theorem cntLeaves_add (depth : ℕ) (f : ℕ → Bool) :
    cntLeaves depth f + cntLeaves depth (fun j => !f j) = 2 ^ depth := by
  unfold cntLeaves
  rw [← List.length_eq_length_filter_add, List.length_range]

end Compile.Disc.Counts

