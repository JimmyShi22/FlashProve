-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/OpenHonest.lean: A VALUE OF `OnlineProverArguments` (Honest/AtPureSixKinds.lean) AT THE
KINDS' OWN TEXTS: the three functions that the filling reads. ONE DEFINITION, WITH CODE, AND ONE
EQUATION. It defines part of what the honest prover reads.

  `openHonest`   `claims`: `K11.headClaimsByPlace` (Honest/K11/ClaimsN.lean) · `pile`:
                 `K13.pileAnyK3` (Honest/K13/PileOfAnySize.lean) · `keyOf`: `K5.keyOfK3`
                 (Honest/K5/Law/KeyOfK3.lean)
  `openHonest_claims`   the one equation

By their types the three read the public part, the ground, the public instance and challenges: no
weight, no coin, no witness. The fields `req`, `cells` and `enc` are not read by `widerFillAt` or
`widerFillAtC` (Honest/AtPureWiderAt.lean, Limits): they are laid at constants that return nothing.

Limits.
  * A definition, and what it lays at one field. That the filling returns at it is not said.
  * `K11.headClaimsByPlace`: a filling at `openHonest` lays it into K11's lot. K11's `FiveAtPure`
    (Honest/K11/Plays/FiveAtPureStatement.lean), at
    `widerFill`, asks "O.claims = headClaimsByPlace": `openHonest_claims` says that `openHonest`
    meets it. At any other filling K11's `FiveAtAnyFill` names the lot's halves at that text.
  * All limits of the three texts hold here, their silent cases among them: where `onlineFirstChainAt`
    rejects, no claim and no row; where the public test `Seat5.keysFit` fails, K5 lays no half at
    that place.
  * `K13.pileAnyK3` makes two of a row's four fields; the mask form and the target are placeholders.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureSixKinds
import Johnson.Desc.ProofFile.Honest.K11.ClaimsN
import Johnson.Desc.ProofFile.Honest.K13.PileOfAnySize
import Johnson.Desc.ProofFile.Honest.K5.Law.KeyOfK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **The open functions at the kinds' own texts.** -/
def openHonest : OnlineProverArguments :=
  { claims := K11.headClaimsByPlace
    pile := K13.pileAnyK3
    req := fun _ => (default, #[])
    keyOf := K5.keyOfK3
    cells := fun _ _ _ => none
    enc := fun _ _ _ _ _ => none }

/-- What K11's `FiveAtPure` asks of the letter `O.claims`. -/
theorem openHonest_claims : openHonest.claims = K11.headClaimsByPlace := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.openHonest
#print axioms ProofFile.Honest.openHonest_claims
