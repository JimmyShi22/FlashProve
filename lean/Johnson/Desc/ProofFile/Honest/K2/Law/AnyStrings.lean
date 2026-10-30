-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AnyStrings.lean: a value of the strings `EAll`
(Johnson/Desc/Sound/FileRule.lean), at any description and any trees left: for a law that asks "any
strings" (y₀ of `claim_at_yes`, `stored_at_yes`, `k2_exchange_full`): every entry a zero or an empty
list. One definition; nothing else.

Limits. IT IS ANY VALUE: it is no reached or honest string, and no law says that a run has it; it
only shows that the type has a value. Nothing on any property.
-/
import Johnson.Desc.Sound.FileRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.Sound (EAll)

/-- **A value of the strings**: every entry zero or empty. -/
def anyStrings (D : OnBytes.Maker.WholeD) (all : List OnBytes.Maker.LeftT) : (EAll D all).Str :=
  (fun _ => (0, []), fun _ => [])

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.anyStrings
