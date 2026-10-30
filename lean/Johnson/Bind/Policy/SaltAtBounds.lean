-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bind/Policy/SaltAtBounds.lean: if the frame that the description lays has salts of 40 bytes
at `storedPublicFiles`, it has them at `zAt C theta cap`, the same public files with the acceptance policy (C,
theta, cap), for every policy with 2 ^ 8 ≤ theta ≤ C < 2 ^ 32 and cap ≤ 1024.

Why. `Bind.Cpp.SaltAt Z` (Johnson/Bind/Cpp/Defs.lean) is a premise of statements that tie the
committer that runs to the committer as mathematics. By Johnson/Bind/Policy/SaltAtPolicies.lean it
is carried from `storedPublicFiles` to all files in scope that differ in the policy alone; by
Johnson/Goal/Files/ScopeAtPolicies.lean the files `zAt C theta cap` within the four bounds are among
these.

Limits. AN IMPLICATION. `SaltAt storedPublicFiles` IS NOT PROVED HERE OR BENEATH: until it is a theorem, this
statement says nothing of any file. This is not `Bind.Cpp.SaltInScope`: files in scope can differ
from `storedPublicFiles` in five more free numbers and in the scale file. All limits of
Johnson/Goal/Description/LaidAtPolicies.lean hold here too. Nothing on binding or on soundness.

-/
import Johnson.Bind.Policy.SaltAtPolicies
import Johnson.Goal.Files.ScopeAtPolicies

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Policy
open VerifierAndGoals FlashProve

/- The named files stay folded: left to unfold them, Lean compares whole files byte by byte and runs
out of stack (Johnson/Goal/Files/FilesReadProof.lean's own note). -/
attribute [local irreducible] storedPublicFiles zAt

/-- **If the frame's salts have 40 bytes at `storedPublicFiles`, they have 40 bytes at `zAt C theta cap`**, for
every policy within the four bounds. An implication: its last premise is proved nowhere here. -/
theorem saltAt_bounds_of_full {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C)
    (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) (h : Bind.Cpp.SaltAt storedPublicFiles) :
    Bind.Cpp.SaltAt (zAt C theta cap) :=
  saltAt_policy_of_full (inScope_zAt h1 h2 h3 h4) (zAt_KL C theta cap) (zAt_pol C theta cap) h

end Bind.Policy

#print axioms Bind.Policy.saltAt_bounds_of_full
