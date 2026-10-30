-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyNineLinesGuards.lean

The closed lines that KeyDoorUClosedGuards.lean does not
have: G_u's members in the shape, the checks of o_u's tree and of the fresh table, and the book's cuts, by
Lean's evaluator, each with a control. KeyNineLinesKernel.lean imports this file.

Limits. Evaluations outside the kernel: no theorem. At `QK`, `keyBook`. Nothing on completeness, on soundness
or on what is hidden.
-/
import E2E.KeyDoorUClosedGuards
import E2E.KeyBookHeldK12

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open AtPublicFiles.KeyBook (atFull keyBook)
open H2K.Member (piKUFull piKOFull)

#eval (colFitsU AQ piKUFull, freshFitsU AQ piKUFull)
#eval atFull fun K => bookCutsU (keyBook K) AQ piKUFull

#eval (shapeU.core.st.groups[shapeU.g]?).map (·.members)

-- Foretold: the group under test has the members 0 and 3. Control: the next group has other members.
#guard (shapeU.core.st.groups[shapeU.g]?).map (·.members) == some [0, 3]
#guard (shapeU.core.st.groups[shapeU.g + 1]?).map (·.members) != some [0, 3]

-- Foretold: yes. Controls, at the other test's place: no.
#guard colFitsU AQ piKUFull
#guard !colFitsU AQ piKOFull
#guard freshFitsU AQ piKUFull
#guard !freshFitsU AQ piKOFull
#guard atFull fun K => bookCutsU (keyBook K) AQ piKUFull
#guard atFull fun K => !bookCutsU (keyBook K) AQ piKOFull

end ProofFile.Honest.K12.Light.KeyDoorUClosed
