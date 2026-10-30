-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineTestRowsByPlace.lean: FOUR OF THE TWENTY-ONE NAMED PREMISES OF `TenRowsOwed` (E2E/OfflineRowsByPlace.lean) AS THEOREMS:
`good` at the rows of the four proximity tests, each in that structure's own type, at the laid simulators and the laid
letters. Calls alone, of E2E/OfflineTestRowsAtFiles.lean.

  `testConditions`       the four rows' letters laid in `TheirConditions`; the other six stay the argument's. Each is read off
                         `k12Letters` (Johnson/Desc/ProofFile/Honest/K12/Sim2/RowsOffline.lean) at its place, over letters that say nothing
  `tests_laid`           `K12Laid` holds at `k12Lists` and at `laidConditions` of these, whatever the other lists and letters
  `rangesTestGood_laid`, `testOnFoldedRowGood_laid`, `testOnOmegaGood_laid`, `ownTestGood_laid`   the four fields of that name

ALL FOUR ARE CONDITIONAL ON THEIR On AT A RUN: with these letters laid, the four fields `rangesTestOwed`, `testOnFoldedRowOwed`,
`testOnOmegaOwed`, `ownTestOwed` of `TenRowsOwed` ask `OnEntry`, `OnEntry`, `OnOmegaKey`, `OnOwnTestEntry` and `budBoth` at a run's own values:
nothing of that is paid here. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineTestRowsAtFiles
import E2E.OfflineRowsByPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open ProofFile.Honest.K12.Sim2 (K12Laid k12Lists k12Letters)
open OnBytes (TableKey)
open AtPublicFiles.KeyBook (KeyPub fullPub rngPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope)

variable {files : PublicFiles} (d : OfflineDescription)

/-- The four tests' letters over letters that say nothing. -/
abbrev testLetters : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness
    TableKey Unit Unit Unit :=
  k12Letters (ConditionsByChain.bare _ offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Unit Unit Unit)
    (offlineSenders (files := files) d) (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0

/-- **The four rows' letters laid**; the other six stay the argument's. -/
def testConditions
    (t : TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit) :
    TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit :=
  { t with
    rangesTest := (testLetters (files := files) d).first rngPlace
    testOnFoldedRow := (testLetters (files := files) d).shared foldedTestPlace
    testOnOmega := (testLetters (files := files) d).shared omegaTestPlace
    ownTest := (testLetters (files := files) d).second ownTestPlace }

/-- **At the laid lists and letters the four rows' simulators, On and bud are their own.** -/
theorem tests_laid (T : TheirSimulators)
    (t : TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit) :
    K12Laid (offlineSenders (files := files) d) (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0
      (k12Lists T d.source d.numbers d.later (offlineSenders (files := files) d))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) (testConditions d t)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
  {K₀ : KeyPub} (hK : fullPub = some K₀) (T : TheirSimulators)
  (t : TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit)
include hs scope hK

/-- **The field `rangesTestGood`.** -/
theorem rangesTestGood_laid :
    GoodFirstAt (files := files) d (laidSimulators (senderValue (files := files) d)
        (k12Lists T d.source d.numbers d.later (offlineSenders (files := files) d)))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) (testConditions d t)) rngPlace :=
  ranges_test_good_at_files d hs scope hK _ _ (tests_laid d T t)

/-- **The field `testOnFoldedRowGood`.** -/
theorem testOnFoldedRowGood_laid :
    GoodSharedAt (files := files) d (laidSimulators (senderValue (files := files) d)
        (k12Lists T d.source d.numbers d.later (offlineSenders (files := files) d)))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) (testConditions d t))
      foldedTestPlace :=
  folded_test_good_at_files d hs scope hK _ _ (tests_laid d T t)

/-- **The field `testOnOmegaGood`.** -/
theorem testOnOmegaGood_laid :
    GoodSharedAt (files := files) d (laidSimulators (senderValue (files := files) d)
        (k12Lists T d.source d.numbers d.later (offlineSenders (files := files) d)))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) (testConditions d t))
      omegaTestPlace :=
  omega_test_good_at_files d hs scope hK _ _ (tests_laid d T t)

/-- **The field `ownTestGood`.** -/
theorem ownTestGood_laid :
    GoodLastAt (files := files) d (laidSimulators (senderValue (files := files) d)
        (k12Lists T d.source d.numbers d.later (offlineSenders (files := files) d)))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) (testConditions d t))
      ownTestPlace :=
  own_test_good_at_files d hs scope hK _ _ (tests_laid d T t)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.tests_laid
#print axioms AtPublicFiles.OfflineRows.rangesTestGood_laid
#print axioms AtPublicFiles.OfflineRows.testOnFoldedRowGood_laid
#print axioms AtPublicFiles.OfflineRows.testOnOmegaGood_laid
#print axioms AtPublicFiles.OfflineRows.ownTestGood_laid
