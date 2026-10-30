-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowQuietIs.lean: the honest side of the kind "lookup" (K3): the
part of a stage that sends nothing, and the form of a simulator beside it (`quiet`, `quietSim`:
Honest/K3/Row.lean), are the frame's own at one round (`quietPart`, `quietSim`:
Honest/ForKinds.lean). Two theorems, each by unfolding alone.

Terms. Honest/K3/GLOSSARY.md ("stage", "frame").

Why. The two texts of Row.lean repeat the frame's, sign for sign. Here Lean shows that they are the
same terms; Row.lean itself is not changed.

Imported. Honest/ForKinds.lean lies beneath this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

/-- The part of a stage that sends nothing is the frame's own part of one round in which nothing is
sent. -/
theorem quiet_is {V W : Type} : (quiet : Part V W Unit) = ProofFile.Honest.quietPart 1 := rfl

/-- The form of a simulator beside it is the frame's own at one round. -/
theorem quietSim_is {Pb : Type} (a : Addr) :
    (quietSim a : Sim Pb) = ProofFile.Honest.quietSim a 1 := rfl

#print axioms ProofFile.Honest.K3.quiet_is
#print axioms ProofFile.Honest.K3.quietSim_is

end ProofFile.Honest.K3
