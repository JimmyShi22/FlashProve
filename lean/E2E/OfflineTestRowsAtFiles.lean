-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineTestRowsAtFiles.lean: the field `good` of `OwedRest` (E2E/OfflineClauses.lean) at the four proximity tests' rows, AT THE
OFFLINE FILE's ROWS AT A DESCRIPTION OF THE PUBLIC FILES (`offlineRowsAt`, E2E/OfflineRowsAtFiles.lean), at the book
`offlineProverCoinCounts`: each in the text of that field's clause with the premise "L.place = p" laid in. Calls alone, of
E2E/OfflineTestRowsGood.lean's four sentences at the description's own senders (`offlineSenders d`): `senderValue d` is
`withTests (offlineSenders d) …` at the description's two places, by unfolding.

  `ranges_test_good_at_files`   the first clause at `rngPlace`
  `folded_test_good_at_files`   the second clause at `foldedTestPlace`
  `omega_test_good_at_files`    the second clause at `omegaTestPlace`
  `own_test_good_at_files`      the third clause at `ownTestPlace`

At S := `laidSimulators (senderValue d) T`, at every T and c at which the four rows' own simulators and letters are laid at the
four places (`K12Laid`, Johnson/Desc/ProofFile/Honest/K12/Sim2/RowsOffline.lean), whatever the six other lists and the other letters.

ALL FOUR ARE CONDITIONAL ON THEIR On AT A RUN (the field `owed`), of which nothing is paid here. The limits of
E2E/OfflineTestRowsGood.lean stand. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineTestRowsGood
import E2E.OfflineRowsAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open OnBytes (TableKey)
open AtPublicFiles.KeyBook (KeyPub fullPub rngPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope)

variable {files : PublicFiles} (d : OfflineDescription)
  (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true) {K₀ : KeyPub}
  (hK : fullPub = some K₀) (T : TheirSimulators)
  (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
    Unit Unit Unit)
  (hc : ProofFile.Honest.K12.Sim2.K12Laid (offlineSenders (files := files) d) (matrixEntryOf matrixReader)
    (multiplicitiesGroups d.source) 0 T c)
include hs scope hK hc

/-- **The first clause at the row of the test on the ranges.** -/
theorem ranges_test_good_at_files :
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
        c).mute.first,
      L.place = rngPlace →
      (L.withField 0 0 (keyFileDescription d.source d.numbers d.later).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription d.source d.numbers d.later) 0) .own
        (keyFileDescription d.source d.numbers d.later).first.blocksInOrder
        (orderOf (keyFileDescription d.source d.numbers d.later)) 0 0
        (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
          c).mute.falls₁ :=
  ranges_test_good scope hs hK (offlineBook_eq hK) (offlineSenders (files := files) d)
    (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0 (senderValue_atAll (files := files) hs scope) T c hc

/-- **The second clause at the row of the test on the folded row's group.** -/
theorem folded_test_good_at_files :
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
        c).mute.shared,
      L.place = foldedTestPlace →
      (L.withField 1 0 (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription d.source d.numbers d.later) 1) .shared
        (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder
        (orderOf (keyFileDescription d.source d.numbers d.later)) 1 0
        (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
          c).mute.falls₂ :=
  folded_test_good scope hs hK (offlineBook_eq hK) (offlineSenders (files := files) d)
    (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0 (senderValue_atAll (files := files) hs scope) T c hc

/-- **The second clause at the row of the test on Omega's group.** -/
theorem omega_test_good_at_files :
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
        c).mute.shared,
      L.place = omegaTestPlace →
      (L.withField 1 0 (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription d.source d.numbers d.later) 1) .shared
        (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder
        (orderOf (keyFileDescription d.source d.numbers d.later)) 1 0
        (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
          c).mute.falls₂ :=
  omega_test_good scope hs hK (offlineBook_eq hK) (offlineSenders (files := files) d)
    (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0 (senderValue_atAll (files := files) hs scope) T c hc

/-- **The third clause at the row of the own test.** -/
theorem own_test_good_at_files :
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
        c).mute.second,
      L.place = ownTestPlace → ∀ base skip,
      (L.withField 2 (keyFileDescription d.source d.numbers d.later).lastChainFirstTreeNumber
          (keyFileDescription d.source d.numbers d.later).second.blocksInOrder base skip).goodAt
        (earlierOf (keyFileDescription d.source d.numbers d.later) 2) .own
        (keyFileDescription d.source d.numbers d.later).second.blocksInOrder
        (orderOf (keyFileDescription d.source d.numbers d.later)) 2
        (keyFileDescription d.source d.numbers d.later).lastChainFirstTreeNumber
        (offlineRowsAt (files := files) d offlineProverCoinCounts (laidSimulators (senderValue (files := files) d) T)
          c).mute.falls₃ :=
  own_test_good scope hs hK (offlineBook_eq hK) (offlineSenders (files := files) d)
    (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0 (senderValue_atAll (files := files) hs scope) T c hc

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.ranges_test_good_at_files
#print axioms AtPublicFiles.OfflineRows.folded_test_good_at_files
#print axioms AtPublicFiles.OfflineRows.omega_test_good_at_files
#print axioms AtPublicFiles.OfflineRows.own_test_good_at_files
