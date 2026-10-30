-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bind/Policy/SaltAtGap.lean: if the frame that the description lays has salts of 40 bytes at
`storedPublicFiles`, it has them at `zGap`. Both are sets of three public files as Ladder/Stored.lean spells
them; `zGap` is `storedPublicFiles` under the policy with limits (C, theta, cap) = (25856, 512, 1).

Why. `Bind.Cpp.SaltAt Z` (Johnson/Bind/Cpp/Defs.lean) is a premise of statements that tie the
committer that runs to the committer as mathematics. In the goals' scope it says that the planner
returns a plan at Z, no more and no less (`saltAt_iff`, Johnson/Bind/Cpp/SaltAt.lean). The planner's
return is carried from `storedPublicFiles` to `zGap` by `laid_gap_of_full`
(Johnson/Goal/Description/LaidAtPolicies.lean).

Limits. AN IMPLICATION. `SaltAt storedPublicFiles` IS NOT PROVED HERE OR BENEATH: until it is a theorem, this
statement says nothing of `zGap`. All limits of Johnson/Goal/Description/LaidAtPolicies.lean hold
here too. Nothing on binding or on soundness.

-/
import Johnson.Bind.Cpp.SaltAt
import Johnson.Goal.Description.LaidAtPolicies

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Policy
open VerifierAndGoals FlashProve

/-- **If the frame's salts have 40 bytes at `storedPublicFiles`, they have 40 bytes at `zGap`.** An implication:
its premise is proved nowhere here. -/
theorem saltAt_gap_of_full (h : Bind.Cpp.SaltAt storedPublicFiles) : Bind.Cpp.SaltAt zGap :=
  (Bind.Cpp.saltAt_iff inScope_gap).2 (laid_gap_of_full ((Bind.Cpp.saltAt_iff inScope_full).1 h))

end Bind.Policy

#print axioms Bind.Policy.saltAt_gap_of_full
