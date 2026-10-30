-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotReadyWhole.lean: the offline part, WITH ALL SIXTEEN SIDES PAID: at the key file's
offline prover and the written book the frame's ready returns, and ReadyDebts
(Johnson/Desc/ProofFile/Honest/Law/ReadyOfSides.lean) holds, WITHOUT the premise LookupsStated.

  LotReadyDebtsWhole     THE STATEMENT: ReadyDebts at keyProver (AtPublicFiles.KeyStandWalked.offlineValue d)
  LotReadyReturnsWhole   THE STATEMENT: there ready returns, at every index in range, every rc, every
                         instance and all coins of a run

They are LotReadyDebts and LotReadyReturns (E2E/LotReadyDebts.lean) with their premise LookupsStated
paid by lookupsStated_offline (E2E/LotLookupsStated.lean). All that the head of E2E/LotReadyDebts.lean
says on what it stands on goes with these two.
Premises.
 1. The test on the public files says yes (protocolDataWellFormed); the files are in scope; offlineDescription
    returns d; fullPub returns the book's data. They have a member: premises_met
    (E2E/LotReadyGuards.lean), at the written copy of the full-size files, where the test's yes is a
    theorem of the side library.
 2. In LotReadyReturnsWhole: the index is in range (matrixInput.inRange). Out of range ready never
    returns (no_ready_out, E2E/LotReadyAtRunCore.lean).
Where it is spent. The accept law's clause AtRunS (E2E/KeyAcceptPairs.lean) as the socket
offlineDebts_from_chains (E2E/OfflineFromChains.lean) asks it: at these very letters: the description
keyFileDescription d.source d.numbers d.later, the prover keyProver (offlineValue d), the book keyBook K₀, at
inputs tied with ok := inRange. AtRunS has one ∃ R over its clauses: ready is a function, so what is
shown of every R that ready returns meets at this R.
Limits. ready says that the rounds are prepared: no round has been played, and nothing says that a
move returns or that a verifier accepts. The written sizes alone. Nothing on soundness,
completeness, hiding or binding.
-/
import E2E.LotReadyDebts
import E2E.LotLookupsStated

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.KeyFile (KeyInst keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- LookupsStated at the object that the stands name. -/
theorem lookupsStated_walked {Z : PublicFiles} {description : OfflineDescription} {K₀ : KeyPub}
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (hK : fullPub = some K₀) :
    LookupsStated K₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description) := by
  have hs := AtPublicFiles.AtFiles.HonestTerm.sourced_of_ok live hd
  exact lookupsStated_offline _ description.source description.numbers description.later _ _ _ _ _ _
    _ hs scope hK

/-- **The debts, all sixteen sides.** -/
def LotReadyDebtsWhole : Prop :=
  ∀ {Z : PublicFiles} {description : OfflineDescription} {K₀ : KeyPub}, protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok description → InScope Z = true → fullPub = some K₀ →
    ReadyDebts (keyFileDescription description.source description.numbers description.later) (keyBook K₀)
      (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description))

/-- **Ready returns.** -/
def LotReadyReturnsWhole : Prop :=
  ∀ {Z : PublicFiles} {description : OfflineDescription} {K₀ : KeyPub}, protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok description → InScope Z = true → fullPub = some K₀ →
    ∀ (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : KeyInst) (k : Coins (keyBook K₀)),
      matrixInput.inRange w₀ = true →
      ∃ R, ready (keyFileDescription description.source description.numbers description.later) (keyBook K₀)
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description)) w₀ rc x k = .ok R

theorem lotReadyDebtsWhole : LotReadyDebtsWhole :=
  fun live hd scope hK => lotReadyDebts live hd scope hK (lookupsStated_walked live hd scope hK)

theorem lotReadyReturnsWhole : LotReadyReturnsWhole :=
  fun live hd scope hK => lotReadyReturns live hd scope hK (lookupsStated_walked live hd scope hK)

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.lookupsStated_walked
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyDebtsWhole
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyReturnsWhole
