-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/AtSecondHashFunction.lean: `theDescription` and `theDescriptionO` are one function, by
definition (Description.lean): `theDescription_O`, `theDescriptionO_older`,
`atOlder_theDescriptionO`.
Limits. Three equations by unfolding. Nothing here is on soundness.

-/
import Johnson.Goal.Description.Description

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace VerifierAndGoals
open VerifiableInference
open FlashProve FlashProve OnBytes.Tie

theorem theDescription_O : theDescription = theDescriptionO := rfl

theorem theDescriptionO_older : theDescriptionO OnBytes.secondHashFunction = theDescription OnBytes.secondHashFunction :=
  rfl

theorem atOlder_theDescriptionO : atSecondHashFunction theDescriptionO = atSecondHashFunction theDescription :=
  theDescriptionO_older

end VerifierAndGoals
