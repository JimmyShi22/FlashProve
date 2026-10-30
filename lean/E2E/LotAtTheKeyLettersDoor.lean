-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotAtTheKeyLettersDoor.lean: THE LAST ASSEMBLY WITH THE LAST CHAIN's THREE FIELDS STRUCK: `TheKeyLots Z d K₀` (AtFullSide/Honest/TheKeyLetters.lean), and so the join's two ends at the letters, FROM ONE NAMED PREMISE:
`BehindTheDoor Z d K₀` (E2E/LotAtTheKeyLetters.lean).

  `lastThree_at_letters`: `LastThree Z d K₀`: `last_three_at_value` (E2E/OfflineLastThree.lean), which holds at every letter, at the letters of the file of letters. One instance.
  **`theKeyLots_of_door`** · **`offlineDebts_of_door`** · **`keyAccepts_of_door`**.

Premises beside the one: offlineDescription Z = .ok d · InScope Z · protocolDataWellFormed (asDescriptionFiles Z) · fullPub = some K₀ (and readFiles Z = .ok pp for the ends).

Limits. AN IMPLICATION. A member of `BehindTheDoor`, under the premises above: behindTheDoor_at_letters (E2E/LotKeyAcceptsAtTheFiles.lean). The three struck fields speak of every stand of the last thread with its letter: that it stands at its first border is
the door's matter. All limits of E2E/LotAtTheKeyLetters.lean and of the files called stand. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotAtTheKeyLetters
import E2E.OfflineLastThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheKeyLetters
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes.Slice (frS)
open AtPublicFiles.Bridge (KeyAccepts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) atTheKeyLettersDoorPad : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) atTheKeyLettersDoorRun : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) atTheKeyLettersDoorRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

/-- **The last chain's three fields at the letters.** -/
theorem lastThree_at_letters (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀) : LastThree Z d K₀ :=
  have h := AtPublicFiles.OfflineRows.last_three_at_value lens numbers (meaning Z) (tableUnused Z K₀) (tests Z d K₀)
    (rest Z K₀) keeps (validShared Z) publicPart d (later Z d K₀) (firstSaid Z d K₀) live hd
    (AtPublicFiles.FirstH.Lots.sourced_of_description hd live) scope hK₀
  ⟨h.1, h.2.1, h.2.2⟩

/-- **`TheKeyLots` FROM «BEHIND THE DOOR» ALONE.** -/
theorem theKeyLots_of_door (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀) (behind : BehindTheDoor Z d K₀) :
    TheKeyLots Z d K₀ :=
  theKeyLots_of_two hd scope live hK₀ (lastThree_at_letters hd scope live hK₀) behind

/-- **The offline clause from «behind the door» alone.** -/
theorem offlineDebts_of_door {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) (behind : BehindTheDoor Z d K₀) :
    ∃ Tied TiedM, OfflineDebts Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes
      runValueBytes (offlineStart d) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 :=
  offlineDebts_of_two hr hd scope live hK₀ (lastThree_at_letters hd scope live hK₀) behind

/-- **The last line from «behind the door» alone.** -/
theorem keyAccepts_of_door {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) (behind : BehindTheDoor Z d K₀) :
    KeyAccepts (offlineProverWithEncodedTable Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes runValueBytes
        (offlineStart d))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_of_two hr hd scope live hK₀ (lastThree_at_letters hd scope live hK₀) behind

end AtFullSide.Honest.TheKeyLetters

#print axioms AtFullSide.Honest.TheKeyLetters.lastThree_at_letters
#print axioms AtFullSide.Honest.TheKeyLetters.theKeyLots_of_door
#print axioms AtFullSide.Honest.TheKeyLetters.offlineDebts_of_door
#print axioms AtFullSide.Honest.TheKeyLetters.keyAccepts_of_door
