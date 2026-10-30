-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/TableNumbers.lean: two numbers of the stored tables at the two sizes of the default
setting, as numerals: the number of row variables and the depth of the tables' code.

Four statements, each evaluated by Lean's kernel (`decide +kernel`). `frS`, `srS`
(OnBytes/Slice/FullRecLink.lean, SmallRecLink.lean) are noncomputable terms: an evaluator cannot
print their fields. Whoever compares them with a shape that a program has planned needs them as
numerals: `fitFull_of_eval`, `fitSmall_of_eval` (Johnson/Flat/FitAt.lean [not in this library]) ask `sh.v = frS.P.v` |
`sh.v = srS.P.v`.

Main names: `frS_v` : frS.P.v = 11; `srS_v` : srS.P.v = 8; `frS_a` : frS.P.T.a = 32;
`srS_a` : srS.P.T.a = 23.

Limits: numbers of two terms of this library. That a program's tables have these numbers is not
said.


-/
import OnBytes.Flat.EntryTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open OnBytes.Slice

theorem frS_v : frS.P.v = 11 := by decide +kernel

theorem srS_v : srS.P.v = 8 := by decide +kernel

theorem frS_a : frS.P.T.a = 32 := by decide +kernel

theorem srS_a : srS.P.T.a = 23 := by decide +kernel

end OnBytes.Flat

#print axioms OnBytes.Flat.frS_v
#print axioms OnBytes.Flat.srS_v
#print axioms OnBytes.Flat.frS_a
#print axioms OnBytes.Flat.srS_a
