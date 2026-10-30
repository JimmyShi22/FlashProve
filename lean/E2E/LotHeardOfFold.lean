-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotHeardOfFold.lean: HeardOfFold (E2E/FirstHEval.lean), IN SCOPE: the verifier's state behind the first
sixteen sub-protocols of the key file's first chain holds its claims on the lookups' keys at the prover's points, on the
fold alone.

  LotHeardOfFold, lotHeardOfFold   ∀ Z, KeySourced Z Xs N Pl → InScope Z = true → HeardOfFold Xs N Pl

By heardAtKeys_of_fold (E2E/LotHeardAtKeys.lean), which is the def's body.

Limits. In scope, at the written sizes: HeardOfFold itself has no premise on Xs, N, Pl; here it is had under the two that its
spenders have at hand. Where the fold returns: that it returns on any rounds is not shown. The claims' points alone.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotHeardAtKeys
import E2E.FirstHEval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.AtFiles (KeySourced)
open VerifierAndGoals (PublicFiles InScope)

/-- **HeardOfFold, in scope.** -/
def LotHeardOfFold : Prop :=
  ∀ {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}, KeySourced Z Xs N Pl →
    InScope Z = true → HeardOfFold Xs N Pl

theorem lotHeardOfFold : LotHeardOfFold := fun hs scope x seen cols s r c h tail =>
  heardAtKeys_of_fold hs scope x seen cols s r c h tail

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.lotHeardOfFold
