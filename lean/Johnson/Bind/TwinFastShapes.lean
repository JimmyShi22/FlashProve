-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastShapes.lean: the committer at the fast encoder is the committer, at the two
shapes of the stored examples.

Johnson/Bind/TwinFastProof.lean proves the equation at every shape with a ≤ 32 and l + r ≤ 2^a. Here
it is drawn at the small stored example's shape (`Anchor.shape`, Johnson/Bind/TwinAnchor.lean) and
at the full size's (`fullShape`, Johnson/Bind/TwinBudget.lean): so both meet the two premises.
Limits. Two instances of one theorem.

-/
import Johnson.Bind.TwinFastProof
import Johnson.Bind.TwinAnchor
import Johnson.Bind.TwinBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

/-- At the small stored example's shape (`Anchor.shape`, Johnson/Bind/TwinAnchor.lean), which meets
the two premises, the committer at the fast encoder is the committer. -/
theorem fast_small {m : Type → Type} [Monad m] [LawfulMonad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (files : List ByteArray)
    (T : Table) :
    commitFastW h Anchor.shape files T = commitW h Anchor.shape files T :=
  commitFastW_is_commitW h _ (by show 23 ≤ 32; decide)
    (by show 524288 + 65535 ≤ 2 ^ 23; decide) files T

/-- At the full size's shape (`fullShape`, Johnson/Bind/TwinBudget.lean), which meets the two
premises, the committer at the fast encoder is the committer. (`Bind.Cpp.shapeFull` is the same
shape: `Bind.Cpp.numerals_are`, Johnson/Bind/Cpp/Defs.lean.) -/
theorem fast_full {m : Type → Type} [Monad m] [LawfulMonad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (files : List ByteArray)
    (T : Table) :
    commitFastW h fullShape files T = commitW h fullShape files T :=
  commitFastW_is_commitW h _ (by show 32 ≤ 32; decide)
    (by show 402653184 + 44040191 ≤ 2 ^ 32; decide) files T

end Bind.Twin

#print axioms Bind.Twin.fast_small
#print axioms Bind.Twin.fast_full
