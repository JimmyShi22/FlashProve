-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K8Q21R/SmallRunAtLinks.lean: Johnson/P5J/SmallRunAt.lean's statement at the closed
constant's own name for the list (`P5J.At.links`, Johnson/P5J/LettersAt.lean): one call.

-/
import Johnson.P5J.SmallRunAt
import Johnson.P5J.LettersAt

set_option autoImplicit false

namespace P5J.At
open VerifiableInference.Desc.First (runsOf)

/-- **`P5J.smallRun_at` (Johnson/P5J/SmallRunAt.lean) at `P5J.At.links`.** -/
theorem smallRun_links (l : ℕ) (hl : l ≤ 24) :
    ∃ sub, P5J.At.links[l]? = some sub ∧
      runsOf sub (5 + if l = 24 then 1 else 0) "small" =
        [(4 + if l = 24 then 1 else 0, "K8.equations")] := P5J.smallRun_at l hl

end P5J.At

#print axioms P5J.At.smallRun_links
