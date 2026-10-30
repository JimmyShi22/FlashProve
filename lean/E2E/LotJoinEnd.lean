-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinEnd.lean: THE END OF THE LAYING, WITH THE SHARED CHAIN's TWO TESTS STRUCK: KeyAccepts of the offline prover, at the empty fall, at the served requests, FROM WHAT IS LEFT OF THE LAST
CHAIN AND THE DOOR ALONE: LeftEnd (E2E/LotJoinAtTheLots.lean) less its four fields on members 9 and 10 of the shared chain, at tt := ttValue (E2E/LotSharedAtValue.lean: texts over the
offline prover's own two jobs).

  `LeftLast`: WHAT IS LEFT, FIVE FIELDS: behind (DoorBehindS, at every R that ready returns) · lastSeat (where U₃ stands: face, chain's number, first tree's number, list, halves; and its test with
    code on four borders: closed facts of a laid U₃) · lastOwes · lastNext · lastYes. NONE SPEAKS OF A MEMBER OF THE FIRST OR THE SHARED CHAIN.
  `leftEnd_of_last`: LeftEnd from it: testU, testOmega, testYesU, testYesOmega by valueTestU … (E2E/LotJoinSharedAtValue.lean); sits by sits_of_last (E2E/OfflineSitsAtLaid.lean); lastList out of lastSeat.
  **`keyAccepts_of_last`**: KeyAccepts from it.

Letters that stay: tk, rest, Z₀ (free: any value serves) and the last chain's U₃, S₃.

Limits. AN IMPLICATION. theKeyLots_of_two (E2E/LotAtTheKeyLetters.lean) builds a member of LeftLast inside its proof, from its two premises; no theorem states it. The four struck fields rest on the files that E2E/LotJoinSharedAtValue.lean calls (its Limits): they count no further than these.
All limits of E2E/LotJoinAtTheLots.lean stand, its ★ among them. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinAtTheLots
import E2E.LotJoinSharedAtValue
import E2E.OfflineSitsAtLaid

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open ProofFile.Honest (Common Coins Table)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open AtPublicFiles.FirstH.Lots (laidFirst laidSaid)
open AtPublicFiles.KeyStandWalked.Lots (ttValue)

local instance (priority := high) padsNonemptyJoinEnd : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) runValueNonemptyJoinEnd : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) runValueInhabitedJoinEnd : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}
  {K₀ : KeyPub} (Z₀ : ProofFile.Pub)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → OnBytes.Means.Words Cb.Gl.E)

/-- **WHAT IS LEFT: THE LAST CHAIN AND THE DOOR.** A premise's form. theKeyLots_of_two (E2E/LotAtTheKeyLetters.lean) builds a member of LeftLast inside its proof, from its two premises; no theorem states it. -/
structure LeftLast (description : OfflineDescription) (U₃ : LastFamily Z description (keyBook K₀))
    (S₃ : OwnLetter Z (keyBook K₀)) : Prop where
  /-- a run: behind the door -/
  behind : ∀ w x (c : CoinOne (keyBook K₀) RunValue RunValue), TiedAt Z description w x →
    ∀ R, ProofFile.Honest.ready (descOf description) (keyBook K₀) (proverOf Z description) w.1 w.2.1 x
        ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R →
      ProofFile.Honest.DoorBehindS (descOf description) (proverOf Z description)
        (laidFirst Z description K₀ w x)
        (namedShared Z₀ tk (ttValue Z description K₀) rest description w x) (U₃ w x)
        (laidSaid Z description K₀ w x)
        (namedSharedSaid Z₀ tk (ttValue Z description K₀) rest description w x) (S₃ w x) x
        ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R
  /-- where the last thread stands, and its test with code -/
  lastSeat : ∀ w x, ((U₃ w x).φ = .own ∧ (U₃ w x).chain = 2 ∧
      (U₃ w x).ft = (descOf description).lastChainFirstTreeNumber ∧
      (U₃ w x).bs = (descOf description).second.blocksInOrder ∧
      (U₃ w x).hs = (proverOf Z description).second) ∧ (U₃ w x).fits 4 = true
  lastOwes : ∀ w x, TiedAt Z description w x → ProofFile.Honest.OwesS (U₃ w x) (S₃ w x)
  lastNext : ∀ w x, TiedAt Z description w x → ∀ b, ProofFile.Honest.SaidNext (U₃ w x) (S₃ w x) b
  lastYes : ∀ w x, TiedAt Z description w x →
    ProofFile.Honest.YesS (U₃ w x) (S₃ w x) (ProofFile.Honest.fallsBy [] (descOf description).second.blocksInOrder)

variable {U₃ : LastFamily Z description (keyBook K₀)} {S₃ : OwnLetter Z (keyBook K₀)}

/-- LeftEnd from it: the shared chain's two tests are struck. -/
theorem leftEnd_of_last (hd : offlineDescription Z = .ok description) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (left : LeftLast Z₀ tk rest description U₃ S₃) :
    LeftEnd Z₀ tk (ttValue Z description K₀) rest description U₃ S₃ where
  behind := left.behind
  lastList := fun w x => (left.lastSeat w x).1.2.2.2.1
  sits := fun w x _ _ => AtPublicFiles.OfflineRows.sits_of_last description ProofFile.Honest.K14.WitLens.words
    AtPublicFiles.KeyStandFull.idleNm (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk (ttValue Z description K₀) rest
    ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀ (AtPublicFiles.FirstH.Lots.laterValue Z description K₀)
    (AtPublicFiles.FirstH.Lots.sourced_of_description hd live) scope w x (U₃ w x) (left.lastSeat w x).1
    (left.lastSeat w x).2
  lastOwes := left.lastOwes
  lastNext := left.lastNext
  lastYes := left.lastYes
  testU := valueTestU tk rest Z₀ hd scope live hK₀
  testOmega := valueTestOmega tk rest Z₀ hd scope live hK₀
  testYesU := valueTestYesU tk rest Z₀ hd scope live hK₀
  testYesOmega := valueTestYesOmega tk rest Z₀ hd scope live hK₀

/-- **THE END: KeyAccepts FROM THE LAST CHAIN's DEBTS AND «BEHIND THE DOOR» ALONE.** -/
theorem keyAccepts_of_last (hd : offlineDescription Z = .ok description) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (left : LeftLast Z₀ tk rest description U₃ S₃) :
    AtPublicFiles.Bridge.KeyAccepts (offlineProverWithEncodedTable Z (descOf description) (thePartsAt Z).book
                  ((thePartsAt Z).prover description) runValueBytes runValueBytes (offlineStart description))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_of_end hr Z₀ tk (ttValue Z description K₀) rest hd scope live hK₀
    (leftEnd_of_last Z₀ tk rest hd scope live hK₀ left)

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.leftEnd_of_last
#print axioms AtPublicFiles.AtFiles.HonestTerm.keyAccepts_of_last
