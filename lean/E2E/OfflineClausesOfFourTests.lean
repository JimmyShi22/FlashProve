-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineClausesOfFourTests.lean: T3's three offline lines at the offline prover's own value, from what
is left when twelve rows and the field runs are paid: good and owed at the four proximity tests' rows.

  FourTestsOwed                          eight named premises: the four tests' good, the four tests' owed.
  fourRowsOwed_of_tests                  with the field runs (runs_text_at_files,
                                         E2E/OfflineRunsAtFiles.lean): FourRowsOwed.
  offline_clauses_of_four_tests          T3's three offline lines under the premises of offline_clauses,
                                         with FourTestsOwed in OwedRest's place.
  offline_clauses_of_four_tests_at_files the same at thePartsAt files, with the files' description under
                                         ∃ and the guard OfflineSidesAreWhole paid.

The simulators: laidSimulators K (k14Lists K T): K the offline prover's own senders; of T the four tests'
lists stay letters. The rows' letters: laidConditions … (withSharedSix K q): the four tests' letters q stay
letters.

CONDITIONAL: FourTestsOwed is a premise here: fourTestsOwed_of_owed (E2E/OfflineClausesOfFourOwed.lean) gives a member from FourOwed. It stands in for the four proximity
tests' proofs (rows 5, 14, 15, 16). So this file proves no zero knowledge of any protocol: it says what
is left. The limits that the heads of the twelve rows' files and of the field runs' files state stand
here too: they are not said again.
-/
import E2E.OfflineRowsJoin
import E2E.OfflineFourRowsLeft
import E2E.OfflineRunsAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open OnBytes (TableKey)
open LPFD.Full (XF)
open AtPublicFiles.KeyBook (rngPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)

variable {files : PublicFiles}

/-- **WHAT STAYS OWED WHEN TWELVE ROWS AND THE FIELD runs ARE PAID**: the four proximity tests' good and
the four tests' owed, each at the row's own place. NAMED PREMISES. fourTestsOwed_of_owed (E2E/OfflineClausesOfFourOwed.lean) gives a member from FourOwed. -/
structure FourTestsOwed (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
    (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit) : Prop where
  rangesTestGood : GoodFirstAt (files := files) d S c rngPlace
  testOnFoldedRowGood : GoodSharedAt (files := files) d S c foldedTestPlace
  testOnOmegaGood : GoodSharedAt (files := files) d S c omegaTestPlace
  ownTestGood : GoodLastAt (files := files) d S c ownTestPlace
  rangesTestOwed : OwedFirstAt (files := files) d S c Rel H rngPlace
  testOnFoldedRowOwed : OwedSharedAt (files := files) d S c Rel H foldedTestPlace
  testOnOmegaOwed : OwedSharedAt (files := files) d S c Rel H omegaTestPlace
  ownTestOwed : OwedLastAt (files := files) d S c Rel H ownTestPlace

variable (d : OfflineDescription)

/-- With the field runs, which is paid at the offline prover's own value. -/
theorem fourRowsOwed_of_tests (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (tests : FourTestsOwed (files := files) d S c (KeyRel files)
      ((partsOfDescription (files := files) d).prover d)) :
    FourRowsOwed (files := files) d S c (KeyRel files)
      ((partsOfDescription (files := files) d).prover d) where
  rangesTestGood := tests.rangesTestGood
  testOnFoldedRowGood := tests.testOnFoldedRowGood
  testOnOmegaGood := tests.testOnOmegaGood
  ownTestGood := tests.ownTestGood
  runs := runs_text_at_files d hd hs scope S c
  rangesTestOwed := tests.rangesTestOwed
  testOnFoldedRowOwed := tests.testOnFoldedRowOwed
  testOnOmegaOwed := tests.testOnOmegaOwed
  ownTestOwed := tests.ownTestOwed

variable (T : TheirSimulators)
  (q : TestConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit)

/-- **T3's THREE OFFLINE LINES FROM THE FOUR PROXIMITY TESTS' ROWS.** -/
theorem offline_clauses_of_four_tests (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (x₀ : XF)
    (tests : FourTestsOwed (files := files) d
      (laidSimulators (senderValue (files := files) d)
        (k14Lists (senderValue (files := files) d) T))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
        (withSharedSix (senderValue (files := files) d) q)) (KeyRel files)
      ((partsOfDescription (files := files) d).prover d)) :
    (∀ i r e, (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d)).ext
        (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
        (offlineSimulatorAt d (partsOfDescription (files := files) d)
          (offlineRowsAt (files := files) d offlineProverCoinCounts
            (laidSimulators (senderValue (files := files) d)
              (k14Lists (senderValue (files := files) d) T))
            (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
              (withSharedSix (senderValue (files := files) d) q)))) ∧
      PrivateStopsAtMost (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 :=
  offline_clauses_of_rows d _ _ live scope hd hs x₀
    (tenRowsOwed_of_four d T q (KeyRel files) _ hs scope live
      (fourRowsOwed_of_tests d hd hs scope _ _ tests))

/-- **THE SAME AT THE NAMED VALUE.** -/
theorem offline_clauses_of_four_tests_at_files (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      thePartsAt files = partsOfDescription d ∧ OfflineSidesAreWhole (thePartsAt files) ∧
      ∀ (T : TheirSimulators)
        (q : TestConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit
          Unit),
        FourTestsOwed (files := files) d
          (laidSimulators (senderValue (files := files) d)
            (k14Lists (senderValue (files := files) d) T))
          (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
            (withSharedSix (senderValue (files := files) d) q)) (KeyRel files)
          ((partsOfDescription (files := files) d).prover d) →
        (∀ i r e, (AtPublicFiles.AtFiles.HonestTerm.offlineProver
            (partsOfDescription (files := files) d)).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
          ExactOutsideStops
            (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
            (workAtFiles files).offline.cleared
            (offlineSimulatorAt d (partsOfDescription (files := files) d)
              (offlineRowsAt (files := files) d offlineProverCoinCounts
                (laidSimulators (senderValue (files := files) d)
                  (k14Lists (senderValue (files := files) d) T))
                (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
                  (withSharedSix (senderValue (files := files) d) q)))) ∧
          PrivateStopsAtMost
            (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named files live
  obtain ⟨-, x₀, -, -⟩ := VerifiableInference.Compilation.someRequestIsServed_holds files scope hr
  exact ⟨d, hd, thePartsAt_ok hd, offlineSides_whole scope live,
    fun T q tests => offline_clauses_of_four_tests d T q live scope hd hs x₀ tests⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.fourRowsOwed_of_tests
#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_four_tests
#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_four_tests_at_files
