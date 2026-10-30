-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/KernelNames.lean: the names that lookAt gives the two lookups of the 24 links in
front of the output head's link are the written names (namesT,
Johnson/AtFull/K3X/KernelTests.lean). A closed fact on strings alone, proved by evaluation in Lean's
kernel, with a negative test: at link 0 the name with the word of the other sort of link is not the
written one.
Limits. Nothing of any public file is read here. Nothing on soundness.

-/
import Johnson.AtFull.K3X.KernelTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X

theorem names_W : namesT = true := by decide +kernel

/-- A negative test. -/
theorem names_no : (nameOf 0 "attention" false == Lots.K3.nameW 0 false) = false := by
  decide +kernel

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.names_W
#print axioms Johnson.AtFull.K3X.names_no
