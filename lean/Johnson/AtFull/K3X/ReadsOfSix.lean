-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/ReadsOfSix.lean: the six statements at each of the 25 links (SixAt,
Johnson/AtFull/K3X/SixAt.lean) give the six hypotheses on the public data in both forms in which the
lookups' rows take them. Joinings; nothing is evaluated.

  **`readsX_of_six`**: (∀ i < 25, SixAt X i) ⊢ ReadsX X (Johnson/AtFull/Desc/Lots/K3RowX.lean). The
    views of the light file are those of the rows' file by definition.
  **`readsXB_of_six`**: the same ⊢ readsXB X = true (Johnson/AtFull/Desc/Lots/K3RowXB.lean), through
    the tie of the light comparison to that one (Johnson/AtFull/Desc/Lots/K3LightTie.lean).

Limits. readsXB is this library's comparison with written values: the verifier does not ask it. That
the six hold at any public data is not said here. Nothing on soundness.

-/
import Johnson.AtFull.K3X.SixAt
import Johnson.AtFull.Desc.Lots.K3LightTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model
open Johnson.AtFull.Lots.K3 (ReadsX readsXB readsXB_light)

/-- **The six hypotheses on the public data, from the 25 links.** -/
theorem readsX_of_six {X : Verify.Public} (h : ∀ i, i < 25 → SixAt X i) : ReadsX X :=
  { calls := fun i hi => (h i hi).calls
    digits := fun i hi => (h i hi).digits
    laid := fun i hi => (h i hi).laid
    key := fun i hi => (h i hi).key
    quiet := fun i hi => (h i hi).quiet
    caller := fun i hi => (h i hi).caller }

/-- **The comparison with code accepts.** -/
theorem readsXB_of_six {X : Verify.Public} (h : ∀ i, i < 25 → SixAt X i) : readsXB X = true :=
  (readsXB_light X).trans (test_of_six h)

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.readsX_of_six
#print axioms Johnson.AtFull.K3X.readsXB_of_six
