-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SecondOwedOf.lean: THE SMALLNESS TEST: `SecondOwed` (Johnson/P1K8R/SecondCount.lean)
FROM ITS FIRST CLAUSE AND `BehindEqs` (Johnson/P1K8R/SecondAtSeat.lean). One lemma; none of the
library's goals. Nothing on completeness, soundness or hiding.

  `secondOwed_of`   the pair
Why a separate file: SecondCount.lean stands over files of the honest side's frame, and
SecondAtSeat.lean does not.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.SecondAtSeat
import Johnson.P1K8R.SecondCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest

/-- `SecondOwed` from its first clause and `BehindEqs`. -/
theorem secondOwed_of {b : Block S Claim} {s : S}
    (h1 : ∀ tl F', s.tl? = some tl → s.fork? = some F' → SecondLaid tl F' ∧
      ∀ g₀ nbW W, tl.heard = some g₀ → tl.wants = some (nbW, W) → PieceLive tl g₀ W)
    (h2 : BehindEqs b s) : SecondOwed b s := ⟨h1, h2⟩

end P1K8

#print axioms P1K8.secondOwed_of
