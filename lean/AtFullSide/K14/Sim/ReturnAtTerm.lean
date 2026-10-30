-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/ReturnAtTerm.lean: THE NAMED PROPOSITION ReturnIsTheDescription, from the body (AtFullSide/K14/Sim/ReturnBody.lean).

  `returnIsTheDescription_at_every_files`   the form with no premise: every return of the online maker
  `returnIsTheDescription`   the proposition: its premises of scope and of the live test are not spent

No property of the protocol is claimed.
-/
import E2E.TheHonestProverStatements
import AtFullSide.K14.Sim.ReturnBody

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- The form with no premise. -/
theorem returnIsTheDescription_at_every_files (files : VerifierAndGoals.PublicFiles) :
    ∀ returned, onlineMaker files = .ok returned →
      ∃ places firstChain, H2U.placesOfMade returned.Z.made = .ok places ∧
        ProofFile.onlineFirstChainAt returned.Z = .ok firstChain ∧
        returned.F = descZ returned.Z places firstChain :=
  fun _ hA => returnIsTheDescription_body hA

/-- **The proposition.** -/
theorem returnIsTheDescription (files : VerifierAndGoals.PublicFiles) : ReturnIsTheDescription files :=
  fun _ _ => returnIsTheDescription_at_every_files files

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.returnIsTheDescription_at_every_files
#print axioms ProofFile.Honest.Term.returnIsTheDescription
