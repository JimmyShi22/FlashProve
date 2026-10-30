-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotReadyShown.lean: A TEST FOR EMPTINESS of LotReadyReturns (E2E/LotReadyDebts.lean): what it gives at
one named case. A conditional on that statement and on one premise, which E2E/LotLookupsStated.lean pays.

  zeroTable       the table's randomness of zeros: a member of (protocolAtFiles Z).EncodingRandomness
  lotReadyShown   from LotReadyReturns: at the library's written full-size files VerifierAndGoals.storedPublicFiles there are a description that
                  offlineDescription returns and the book's data that fullPub returns such that, IF LookupsStated HOLDS THERE,
                  ready returns at these named letters: the index matrixInput.dummy, the table's randomness of zeros, the
                  instance written of the record of zeros (keyInstanceOfOutOfDomainSample recZeroFull), and the default coins of a run.

THE CASE IS SHOWN ONLY UNDER LookupsStated K₀ (offlineValue description) (a named premise, E2E/OfflineLaying.lean: the
parts of the two lookups' rows state what the book has for them). IT IS NOT PROVED IN THIS FILE: lookupsStated_walked
(E2E/LotReadyWhole.lean) proves it, and lotReadyShownWhole (E2E/LotReadyWholeAtRun.lean) is this case without the premise. The four other premises of LotReadyReturns and «the
index is in range» are met here by theorems (E2E/LotReadyGuards.lean's pieces); protocolDataWellFormed at storedPublicFiles is the SIDE library's.

Limits. The instance is not tied to the index or to the table's randomness: ready reads no such tie. ready says that the rounds
are prepared: no round is played. VerifierAndGoals.storedPublicFiles is three terms written in Lean. Nothing on soundness, completeness, hiding or
binding.
-/
import E2E.LotReadyDebts
import E2E.LotReadyGuards
import Johnson.Flat.ThreeAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open VerifiableInference.OnPublicFiles (recZeroFull)
open OnBytes.Slice (frS)
open AtPublicFiles.KeyFile (KeyInst keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub full_made)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription)

/-- The table's randomness of zeros. -/
def zeroTable : TableR frS 402653181 := (fun _ _ => 0, fun _ _ => 0)

/-- **What LotReadyReturns gives at the written full-size files, under LookupsStated.** -/
theorem lotReadyShown (h : LotReadyReturns) :
    ∃ (description : OfflineDescription) (K₀ : KeyPub),
      offlineDescription VerifierAndGoals.storedPublicFiles = .ok description ∧ fullPub = some K₀ ∧
      (LookupsStated K₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := VerifierAndGoals.storedPublicFiles) description) →
        ∃ R, ready (keyFileDescription description.source description.numbers description.later) (keyBook K₀)
          (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := VerifierAndGoals.storedPublicFiles) description))
          matrixInput.dummy (zeroTable : (protocolAtFiles VerifierAndGoals.storedPublicFiles).EncodingRandomness) (keyInstanceOfOutOfDomainSample recZeroFull) default = .ok R) := by
  obtain ⟨d, hd, -⟩ :=
    AtPublicFiles.LotPlanGround.offlineDescriptionNamed VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK⟩ := full_made
  exact ⟨d, K₀, hd, hK, fun hL => h AtFullSide.Top.theLive_zFull hd VerifierAndGoals.inScope_full hK hL
    matrixInput.dummy zeroTable (keyInstanceOfOutOfDomainSample recZeroFull) default AtPublicFiles.LotReadyGuards.dummy_inRange⟩

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyShown
