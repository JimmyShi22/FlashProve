-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineAtTheLetters.lean: the offline clause and the last line of the join at the letters of AtFullSide/Honest/TheKeyLetters.lean.

Main names. `offlineDebts_at_letters`, `keyAccepts_at_letters`.

What stays open. `TheKeyLots`, and the files' premises `hr`, `hd`, `scope`, `live`, `hK₀`.

No law over coins. Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import AtFullSide.Honest.TheKeyLetters
import E2E.OfflineJoinLaws
import E2E.OfflineLastTerms

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.Honest.TheKeyLetters
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Common Coins Table Fall)
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.AtKey (keepsKey)
open AtPublicFiles.Bridge (KeyAccepts)
open AtPublicFiles.KeyStandFull (idleNm idleMg pub_exists)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.FirstH.Lots (laterValue joinThread joinSaid)
open AtPublicFiles.KeyStandWalked.Lots (ttValue)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) instNonemptyPadZOfflineAtTheLetters : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyRunValueOfflineAtTheLetters : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) instInhabitedRunValueOfflineAtTheLetters : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

/-- **The offline clause at the letters.** A conditional. -/
theorem offlineDebts_at_letters {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) (L : TheKeyLots Z d K₀) :
    ∃ Tied TiedM, OfflineDebts Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes
      runValueBytes (offlineStart d) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 :=
  offlineDebts_at_value hr (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀) publicPart hd scope live hK₀ L

/-- **The last line at the letters.** A conditional. -/
theorem keyAccepts_at_letters {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) (L : TheKeyLots Z d K₀) :
    KeyAccepts (offlineProverWithEncodedTable Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes runValueBytes
        (offlineStart d))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_at_value hr (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀) publicPart hd scope live hK₀ L

end AtFullSide.Honest.TheKeyLetters

#print axioms AtFullSide.Honest.TheKeyLetters.offlineDebts_at_letters
#print axioms AtFullSide.Honest.TheKeyLetters.keyAccepts_at_letters
