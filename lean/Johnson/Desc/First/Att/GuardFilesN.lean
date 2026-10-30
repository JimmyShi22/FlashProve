-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardFilesN.lean: the tests on public data at the attention segments of the
first chain (Johnson/Desc/First/Att/GuardN.lean), from the three public files, with the public
record made by Model.Verify.publicOf.

  `k5AsksFilesN pol lay KL`: the tests of every attention segment (k5AsksN) of the record that
    Model.Verify.publicOf pol KL (some lay) returns; where that refuses, one test fails.

publicOf calls the second hash function by
name, so this list is not for a verifier whose text takes that hash as a letter: that verifier asks
Johnson/Desc/First/Att/GuardO.lean's rows. This file is kept for what has been run and proved at it:
the runs at the stored sets' own public files, and the laws that carry a yes of this list to the
rows at every o (Johnson/Desc/First/Att/GuardAtSeat.lean). No Mathlib is below this file. A
definition with code; no theorem. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.GuardN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

/-- The same from the three public files: the policy, the layout, the file of scales. -/
def k5AsksFilesN (pol lay KL : ByteArray) : List (String × Bool) :=
  match Model.Verify.publicOf pol KL (some lay) with
  | .ok W => k5AsksN W
  | .error _ => [("k5-public-record: the public files make no record", false)]

end VerifiableInference.Desc.First.Att.P
