-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotEntersFirstAtTerm.lean: THE FIRST CHAIN BEGINS AT THE OFFLINE PROVER's OWN SENDERS: at
offlineValue description (E2E/KeyStandWalked.lean: the senders WITH the four proximity tests), which is what the
offline prover's term runs. No premise on the range.

  `offlineValue_inRange`: these senders' test on the index is matrixInput.inRange: by unfolding.
  `prover_is`: the prover of the term's parts at a description is keyProver at these senders: by unfolding.
  **`entersFirst_atTerm`**: Enters₁ at T₁, in scope, at every matrix, committer's coins, instance, book and
    run's coins at which ready returns and Q.Rel holds.

Limits. Those of E2E/LotEntersFirstCore.lean and E2E/LotEntersFirstTie.lean. UNDER «ready returns»: shown nowhere
here. It says nothing of what the senders send. Q.Rel is a letter: whoever calls this lays it; FOR THE CALLER:
at a relation under which a tied matrix may be out of range, ready refuses there, so a premise "at every tied
input ready returns" is false: the relation has to give matrixInput.inRange. What a run's start owes beside
Enters₁ is not here.
-/
import E2E.LotEntersFirstTie
import E2E.KeyStandWalked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.FirstH.Lots
open ProofFile.Honest
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open ProofFile.Honest.Term (matrixInput)
open VerifierAndGoals (PublicFiles InScope)

variable {files : PublicFiles}

/-- The prover's own senders bear the test "the matrix holds an index". -/
theorem offlineValue_inRange (description : OfflineDescription) :
    (offlineValue (files := files) description).inRange = matrixInput.inRange := rfl

/-- The prover of the term's parts is the key file's prover at these senders. -/
theorem prover_is (description : OfflineDescription) :
    (AtPublicFiles.AtFiles.HonestTerm.partsOfDescription (files := files) description).prover description =
      AtPublicFiles.KeyFile.keyProver (offlineValue (files := files) description) := rfl

/-- **The first chain begins at the offline prover's own senders**, with no premise on the range. -/
theorem entersFirst_atTerm {Bk : ProverCoinCounts} (description : OfflineDescription)
    (hs : KeySourced files description.source description.numbers description.later)
    (scope : InScope files = true) (Q : LaterFill Bk FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness) (M : FullSizeMatrix)
    (rc : (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness) (x : VerifiableInference.Desc.Key.Xi) (rel : Q.Rel M rc x)
    (k : Coins Bk) (R)
    (hR : ready (AtPublicFiles.AtFiles.keyFileDescription description.source description.numbers description.later) Bk
      (AtPublicFiles.KeyFile.keyProver (offlineValue (files := files) description)) M rc x k = .ok R) :
    Enters₁ (AtPublicFiles.AtFiles.keyFileDescription description.source description.numbers description.later)
      (AtPublicFiles.KeyFile.keyProver (offlineValue (files := files) description))
      (Th description.source description.numbers description.later
        (offlineValue (files := files) description) matrixReader Q M rc x) M rc x k R :=
  entersFirst_atValue hs scope _ (offlineValue_inRange description) Q M rc x rel k R hR

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.offlineValue_inRange
#print axioms AtPublicFiles.FirstH.Lots.prover_is
#print axioms AtPublicFiles.FirstH.Lots.entersFirst_atTerm
