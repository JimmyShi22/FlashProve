-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LinkScalarsAreWritten.lean: a premise's form, by name: at a public
record, the number of scalars that each of the twelve layers' links and each of the twelve attention links
sends is the library's written one. One definition; no theorem.

  `LinkScalarsAreWritten X`   for g < 12: the plan X.G[g] has ns = `nsW (sortOf (2 g))` (4059 at link 0, 4058 at
                              the other layers' links) and the plan X.A[g] has nMsg = `nsW 1` (4190):
                              `nsW`, `sortOf`: Johnson/AtFull/Desc/Lots/K3Written.lean

What it is for. The first scalar of the lookup on the digits of such a link is that number less the lookup's
own scalars (`digits_lay`, Honest/K3/Good/Live/WindowsLay.lean; `digits_att`, Honest/K3/Good/Live/Windows.lean).
AtFullSide/Honest/K3/Term/LookupThreeTestsUnderTheHead.lean spends it.

Limits. A definition: nothing says here that any record meets it; under the head
AtFullSide/Honest/K3/Term/LinkScalarsAreWrittenUnderTheHead.lean does. At an attention plan that the maker made nMsg
is ns (`planA_nMsg`, Johnson/AtFull/Shape/DigitsFree.lean). The head's link is not spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.AtFull.Desc.Lots.K3Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open Johnson.AtFull.Lots.K3 (sortOf nsW)

/-- **The 24 links off the head send the written numbers of scalars.** -/
def LinkScalarsAreWritten (X : OnBytes.Model.Verify.Public) : Prop :=
  ∀ g, g < 12 →
    (∀ hp, X.G[g]? = some hp → hp.ns = nsW (sortOf (2 * g))) ∧
    (∀ a, X.A[g]? = some a → a.nMsg = nsW 1)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.LinkScalarsAreWritten
