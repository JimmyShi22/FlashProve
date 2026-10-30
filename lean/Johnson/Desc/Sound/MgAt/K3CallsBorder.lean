--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3CallsBorder.lean: THE LOOKUP ON A LINK's CALLS: THE NUMBER OF THE BORDER
IN FRONT OF IT, IN THE HOUSE's TERM (kOfCalls l, Johnson/Desc/Sound/MgAt/K3CallsTable.lean), IS THE
KIND's LEDGER's (k3K l false, Johnson/Desc/First/Look/K3Base.lean): so that what stands at kOfCalls
l (othersPub_att_mgAll, othersPub_lay_mgAll, othersP_mgAll) is rewritten to the ledger's letter in
one step. One equation of numbers. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: two terms for one number.
USER: nobody yet. Meant: the kind's lead's assembly of its ledger.
LETTERS: l: any number.

Main name: `kOfCalls_k3K`.

Limits. The calls' borders (not the digits').
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsTests
import Johnson.Desc.First.Look.K3Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles

/-- **The two terms are one number.** -/
theorem kOfCalls_k3K (l : ℕ) : kOfCalls l = k3K l false :=
  (kOfCalls_border l).trans rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.kOfCalls_k3K
