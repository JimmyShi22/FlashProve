-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Honest.lean: the honest side. One named part of `VerifierAndGoals.theDescription`
(Description.lean), in a file of its own.
State: a place-holder. `theHonest`: no randomness, a commitment of zeros, a prover that hands empty
files. Nothing on completeness or hiding can be said at it. Nor on correctness of extraction,
opening-form binding, no two openings or anything else that names the honest committer: its `commit`
is one constant, whatever the weights (`FlashProve.fixedCommitterAndProver`, Johnson/Goal/Tie/DescriptionOfData.lean).

-/
import Johnson.Goal.Tie.DescriptionOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve

def theHonest : FlashProve.CommitterAndProver FlashProve.FormBytes := FlashProve.fixedCommitterAndProver

end FlashProve
