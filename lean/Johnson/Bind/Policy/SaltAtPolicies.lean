-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bind/Policy/SaltAtPolicies.lean: if the frame that the description lays has salts of 40
bytes at `storedPublicFiles`, it has them at all public files in the goals' scope that differ from `storedPublicFiles` in
the numbers C, theta, cap of the acceptance policy alone.

Why. `Bind.Cpp.SaltAt Z` (Johnson/Bind/Cpp/Defs.lean) is a premise of statements that tie the
committer that runs to the committer as mathematics. In scope it says that the planner returns a
plan at Z, no more and no less (`saltAt_iff`, Johnson/Bind/Cpp/SaltAt.lean). The planner's return is
carried by `laid_at_policy_of_full` (Johnson/Goal/Description/LaidAtPolicies.lean).

Limits. AN IMPLICATION. `SaltAt storedPublicFiles` IS NOT PROVED HERE OR BENEATH: until it is a theorem, this
statement says nothing of any file. That Z is in scope is a premise. This is not
`Bind.Cpp.SaltInScope`: files in scope can differ from `storedPublicFiles` in five more free numbers and in the
scale file. All limits of Johnson/Goal/Description/LaidAtPolicies.lean hold here too. Nothing on
binding or on soundness.

-/
import Johnson.Bind.Cpp.SaltAt
import Johnson.Goal.Description.LaidAtPolicies

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Policy
open VerifierAndGoals FlashProve

/-- **If the frame's salts have 40 bytes at `storedPublicFiles`, they have 40 bytes at all public files in scope
that differ from `storedPublicFiles` in the numbers C, theta, cap alone.** An implication: its last premise is
proved nowhere here. -/
theorem saltAt_policy_of_full {Z : PublicFiles} {C theta cap : Nat} (hZ : InScope Z = true)
    (hK : Z.KL = storedPublicFiles.KL)
    (hpol : Z.pol = policyFile { storedLines with C := C, theta := theta, cap := cap })
    (h : Bind.Cpp.SaltAt storedPublicFiles) : Bind.Cpp.SaltAt Z :=
  (Bind.Cpp.saltAt_iff hZ).2
    (laid_at_policy_of_full hZ hK hpol ((Bind.Cpp.saltAt_iff inScope_full).1 h))

end Bind.Policy

#print axioms Bind.Policy.saltAt_policy_of_full
