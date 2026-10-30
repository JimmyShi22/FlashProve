-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/MadeAtLaws.lean: one law on what is made of the three public files with
the digest and the second hash function as arguments (`madeOfAtO`, MadeAt.lean beside this file).

It is a tool: it holds of all public files and digests, and no description of the protocol is named.

  `madeOfAtO_older`: madeOfAtO secondHashFunction pol lay KL c = madeOfAt pol lay KL c
    (Johnson/Desc/Ok/NumberPrices/AtDigest.lean). So every law on what `madeOfAt` returns holds of
    what `madeOfAtO secondHashFunction` returns.

Limits. The equation is at `secondHashFunction` alone. At another o nothing says that `madeOfAtO o` returns a
value. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.MadeAt
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes
open VerifiableInference.Number (madeOfAt)

/-- **At the second hash function itself the new text is the old text.** -/
theorem madeOfAtO_older (pol lay KL c : ByteArray) :
    madeOfAtO secondHashFunction pol lay KL c = madeOfAt pol lay KL c := by
  unfold madeOfAtO madeOfAt
  rw [plannedAtO_older]

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.madeOfAtO_older
