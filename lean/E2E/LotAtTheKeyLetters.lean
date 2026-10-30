-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotAtTheKeyLetters.lean: THE LAST ASSEMBLY AT THE NAMES OF THE FILE OF LETTERS: `TheKeyLots Z d K₀` (AtFullSide/Honest/TheKeyLetters.lean: `TheLots` with no letter left) FROM TWO NAMED PREMISES, every other field being
one instance of a top that lies; and so the join's two ends at the letters.

  `LastThree Z d K₀`: THE FIRST PREMISE: the last chain's three fields at `lastThreadAt`, `lastSaidAt`: OwesS · SaidNext at every border · YesS at no fall; at every tied input.
  `BehindTheDoor Z d K₀`: THE SECOND: `DoorBehindS` at the three threads and letters of the file of letters, at every tied input and every R that `ready` returns.
  `lastSeat_at_letters`: where the last thread stands (face, chain's number, first tree's number, list, halves) and its test with code on four borders: closed facts of the laid term.
  **`theKeyLots_of_two`**: `TheKeyLots` from the two.
  **`offlineDebts_of_two`, `keyAccepts_of_two`**: the join's two ends from the two.

WHICH TOP FILLS WHICH FIELD (through E2E/LotJoinAtTheLots.lean's `theLots_of_end` and E2E/LotJoinEnd.lean's `leftEnd_of_last`, at tk := tableUnused, tt := tests, rest := rest, Z₀ := publicPart, U₃ := lastThreadAt, S₃ := lastSaidAt):
  sits: `sits_of_last` (E2E/OfflineSitsAtLaid.lean) at `lastSeat_at_letters` · firstOwes, firstYes: `joinFirstOwes`, `joinFirstYes` at `leftJoin_laid` · firstNext: `joinFirstNext` ·
  testU, testOmega, testYesU, testYesOmega: `valueTestU` … (E2E/LotJoinSharedAtValue.lean) · run: `runFromBehind` (E2E/LotJoinRunDoor.lean) from the second premise · lastOwes, lastNext, lastYes: the first premise.
EACH FITS BY UNFOLDING: no step is paid here: `firstThread` is `laidFirst`, `sharedThreadAt` is `namedShared` at these values, by the abbreviations' own texts.

Premises beside the two: offlineDescription Z = .ok d · InScope Z · protocolDataWellFormed (asDescriptionFiles Z) · fullPub = some K₀ (and readFiles Z = .ok pp for the ends).

Limits. AN IMPLICATION. Members of the two premises, under the four premises above: lastThree_at_letters (E2E/LotAtTheKeyLettersDoor.lean), behindTheDoor_at_letters (E2E/LotKeyAcceptsAtTheFiles.lean). All limits of the files called stand: the four fields on members 9 and 10 rest on another house's files of the
«ready returns» inside `run` rests on what E2E/LotReadyWhole.lean's head says. Nothing on soundness, completeness, hiding or binding.
-/
import AtFullSide.Honest.TheKeyLetters
import E2E.OfflineAtTheLetters
import E2E.LotJoinEnd

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
open ProofFile.Honest (OwesS YesS SaidNext DoorBehindS ready fallsBy)
open AtPublicFiles.Bridge (KeyAccepts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) atTheKeyLettersPad : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) atTheKeyLettersRun : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) atTheKeyLettersRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- **THE FIRST NAMED PREMISE: the last chain's three fields.** A member, under the file's four premises: lastThree_at_letters (E2E/LotAtTheKeyLettersDoor.lean). -/
structure LastThree : Prop where
  owes : ∀ w x, TiedAt Z d w x → OwesS (lastThreadAt Z d K₀ w x) (lastSaidAt Z d K₀ w x)
  next : ∀ w x, TiedAt Z d w x → ∀ b, SaidNext (lastThreadAt Z d K₀ w x) (lastSaidAt Z d K₀ w x) b
  yes : ∀ w x, TiedAt Z d w x →
    YesS (lastThreadAt Z d K₀ w x) (lastSaidAt Z d K₀ w x) (fallsBy [] (descOf d).second.blocksInOrder)

/-- **THE SECOND NAMED PREMISE: behind the door.** A member, under the file's four premises: behindTheDoor_at_letters (E2E/LotKeyAcceptsAtTheFiles.lean). -/
def BehindTheDoor : Prop :=
  ∀ w x (c : CoinOne (keyBook K₀) RunValue RunValue), TiedAt Z d w x →
    ∀ R, ready (descOf d) (keyBook K₀) (proverOf Z d) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R →
      DoorBehindS (descOf d) (proverOf Z d) (firstThread Z d K₀ w x) (sharedThreadAt Z d K₀ w x)
        (lastThreadAt Z d K₀ w x) (firstSaid Z d K₀ w x) (sharedSaidAt Z d K₀ w x)
        (lastSaidAt Z d K₀ w x) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R

variable {Z d K₀}

/-- **Where the last thread stands, and its test with code.** -/
theorem lastSeat_at_letters (hs : KeySourced Z d.source d.numbers d.later) :
    ∀ w x, ((lastThreadAt Z d K₀ w x).φ = .own ∧ (lastThreadAt Z d K₀ w x).chain = 2 ∧
      (lastThreadAt Z d K₀ w x).ft = (descOf d).lastChainFirstTreeNumber ∧
      (lastThreadAt Z d K₀ w x).bs = (descOf d).second.blocksInOrder ∧
      (lastThreadAt Z d K₀ w x).hs = (proverOf Z d).second) ∧ (lastThreadAt Z d K₀ w x).fits 4 = true :=
  fun _ _ => ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
    AtPublicFiles.KeyLastQuiet.fits_last_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs.named.plan⟩

/-- **`TheKeyLots` FROM THE TWO.** -/
theorem theKeyLots_of_two (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀) (last : LastThree Z d K₀)
    (behind : BehindTheDoor Z d K₀) : TheKeyLots Z d K₀ :=
  theLots_of_end publicPart (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀) hd scope live hK₀
    (leftEnd_of_last publicPart (tableUnused Z K₀) (rest Z K₀) hd scope live hK₀
      { behind := behind
        lastSeat := lastSeat_at_letters (AtPublicFiles.FirstH.Lots.sourced_of_description hd live)
        lastOwes := last.owes
        lastNext := last.next
        lastYes := last.yes })

/-- **The offline clause from the two.** -/
theorem offlineDebts_of_two {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) (last : LastThree Z d K₀) (behind : BehindTheDoor Z d K₀) :
    ∃ Tied TiedM, OfflineDebts Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes
      runValueBytes (offlineStart d) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 :=
  offlineDebts_at_letters hr hd scope live hK₀ (theKeyLots_of_two hd scope live hK₀ last behind)

/-- **The last line from the two.** -/
theorem keyAccepts_of_two {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hK₀ : fullPub = some K₀) (last : LastThree Z d K₀) (behind : BehindTheDoor Z d K₀) :
    KeyAccepts (offlineProverWithEncodedTable Z (descOf d) (thePartsAt Z).book ((thePartsAt Z).prover d) runValueBytes runValueBytes
        (offlineStart d))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_at_letters hr hd scope live hK₀ (theKeyLots_of_two hd scope live hK₀ last behind)

end AtFullSide.Honest.TheKeyLetters

#print axioms AtFullSide.Honest.TheKeyLetters.lastSeat_at_letters
#print axioms AtFullSide.Honest.TheKeyLetters.theKeyLots_of_two
#print axioms AtFullSide.Honest.TheKeyLetters.offlineDebts_of_two
#print axioms AtFullSide.Honest.TheKeyLetters.keyAccepts_of_two
