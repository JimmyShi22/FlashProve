-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineClausesOfFourOwed.lean: T3's three offline lines at the offline prover's own value, from what
is left when all sixteen rows' good, the field runs and twelve rows' owed are paid: owed at the four
proximity tests' rows.

  theSimulators, theLetters             the sixteen lists and the one value of the rows' letters at which
                                        all that is paid is paid: no letter is left in either.
  FourOwed                              four named premises: owed at the test on the ranges, at the tests
                                        on the folded row and on Omega, and at the last chain's test.
  fourTestsOwed_of_owed                 with the four tests' good (E2E/OfflineTestRowsByPlace.lean):
                                        FourTestsOwed.
  offline_clauses_of_four_owed          T3's three offline lines under the premises of offline_clauses.
  offline_clauses_of_four_owed_at_files the same at thePartsAt files, with the files' description under ∃
                                        and the guard OfflineSidesAreWhole paid.

The ten lists that laidSimulators leaves open are laid: the shared chain's six by k14Lists, the four
tests' by k12Lists, over lists that are empty. The ten letters likewise: the six rows' own, and the four
tests' (testConditions).

CONDITIONAL: FourOwed is a premise here: fourOwed_of_spent (E2E/OfflineClausesOfLots.lean) gives a member from LotsSpent. At these letters each of the four asks,
at every run that has returned, the test's own condition at the part's start and its bound on the
positions read: these are not «True». So this file proves no zero knowledge of any protocol: it
says what is left. The limits that the heads of the sixteen rows' files and of the field runs' files
state stand here too: they are not said again.
-/
import E2E.OfflineClausesOfFourTests
import E2E.OfflineTestRowsByPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open ProofFile.Honest.K12.Sim2 (k12Lists)
open OnBytes (TableKey)
open LPFD.Full (XF)
open AtPublicFiles.KeyBook (rngPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)

variable {files : PublicFiles} (d : OfflineDescription)

/-- Ten empty lists, over which the ten are laid. -/
def noLists : TheirSimulators := ⟨[], [], [], [], [], [], [], [], [], []⟩

/-- The four tests' lists, over the empty ones. -/
abbrev testLists : TheirSimulators :=
  k12Lists noLists d.source d.numbers d.later (offlineSenders (files := files) d)

/-- **The sixteen lists of simulators.** -/
abbrev theSimulators : OfflineSimulators :=
  laidSimulators (senderValue (files := files) d)
    (k14Lists (senderValue (files := files) d) (testLists (files := files) d))

/-- The four tests' letters. -/
def theTestLetters :
    TestConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit where
  rangesTest := (testLetters (files := files) d).first rngPlace
  testOnFoldedRow := (testLetters (files := files) d).shared foldedTestPlace
  testOnOmega := (testLetters (files := files) d).shared omegaTestPlace
  ownTest := (testLetters (files := files) d).second ownTestPlace

/-- **The one value of the rows' letters.** -/
abbrev theLetters : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix
    (protocolAtFiles files).EncodingRandomness TableKey Unit Unit Unit :=
  laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
    (withSharedSix (senderValue (files := files) d) (theTestLetters (files := files) d))

/-- The lists are the four tests' lists laid over the shared chain's six. -/
theorem theSimulators_eq :
    theSimulators (files := files) d = laidSimulators (senderValue (files := files) d)
      (k12Lists (k14Lists (senderValue (files := files) d) noLists) d.source d.numbers d.later
        (offlineSenders (files := files) d)) := rfl

/-- The letters are the four tests' letters laid over the shared chain's six. -/
theorem theLetters_eq :
    theLetters (files := files) d = laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
      (testConditions d (withSharedSix (senderValue (files := files) d)
        (theTestLetters (files := files) d))) := rfl

/-- **WHAT STAYS OWED**: owed at the four proximity tests' rows. NAMED PREMISES. fourOwed_of_spent (E2E/OfflineClausesOfLots.lean) gives a member from LotsSpent. -/
structure FourOwed : Prop where
  rangesTestOwed : OwedFirstAt (files := files) d (theSimulators (files := files) d) (theLetters (files := files) d) (KeyRel files)
    ((partsOfDescription (files := files) d).prover d) rngPlace
  testOnFoldedRowOwed : OwedSharedAt (files := files) d (theSimulators (files := files) d) (theLetters (files := files) d)
    (KeyRel files) ((partsOfDescription (files := files) d).prover d) foldedTestPlace
  testOnOmegaOwed : OwedSharedAt (files := files) d (theSimulators (files := files) d) (theLetters (files := files) d) (KeyRel files)
    ((partsOfDescription (files := files) d).prover d) omegaTestPlace
  ownTestOwed : OwedLastAt (files := files) d (theSimulators (files := files) d) (theLetters (files := files) d) (KeyRel files)
    ((partsOfDescription (files := files) d).prover d) ownTestPlace

/-- With the four tests' good, which is paid. -/
theorem fourTestsOwed_of_owed (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) (owed : FourOwed (files := files) d) :
    FourTestsOwed (files := files) d (theSimulators (files := files) d) (theLetters (files := files) d) (KeyRel files)
      ((partsOfDescription (files := files) d).prover d) := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact
    { rangesTestGood := by
        rw [theSimulators_eq, theLetters_eq]
        exact rangesTestGood_laid d hs scope hK _ _
      testOnFoldedRowGood := by
        rw [theSimulators_eq, theLetters_eq]
        exact testOnFoldedRowGood_laid d hs scope hK _ _
      testOnOmegaGood := by
        rw [theSimulators_eq, theLetters_eq]
        exact testOnOmegaGood_laid d hs scope hK _ _
      ownTestGood := by
        rw [theSimulators_eq, theLetters_eq]
        exact ownTestGood_laid d hs scope hK _ _
      rangesTestOwed := owed.rangesTestOwed
      testOnFoldedRowOwed := owed.testOnFoldedRowOwed
      testOnOmegaOwed := owed.testOnOmegaOwed
      ownTestOwed := owed.ownTestOwed }

/-- **T3's THREE OFFLINE LINES FROM owed AT THE FOUR PROXIMITY TESTS' ROWS.** -/
theorem offline_clauses_of_four_owed (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (x₀ : XF)
    (owed : FourOwed (files := files) d) :
    (∀ i r e, (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d)).ext
        (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
        (offlineSimulatorAt d (partsOfDescription (files := files) d)
          (offlineRowsAt (files := files) d offlineProverCoinCounts (theSimulators (files := files) d) (theLetters (files := files) d))) ∧
      PrivateStopsAtMost (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 :=
  offline_clauses_of_four_tests d (testLists (files := files) d) (theTestLetters (files := files) d)
    live scope hd hs x₀ (fourTestsOwed_of_owed d hs scope owed)

/-- **THE SAME AT THE NAMED VALUE.** -/
theorem offline_clauses_of_four_owed_at_files (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      thePartsAt files = partsOfDescription d ∧ OfflineSidesAreWhole (thePartsAt files) ∧
      (FourOwed (files := files) d →
        (∀ i r e, (AtPublicFiles.AtFiles.HonestTerm.offlineProver
            (partsOfDescription (files := files) d)).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
          ExactOutsideStops
            (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
            (workAtFiles files).offline.cleared
            (offlineSimulatorAt d (partsOfDescription (files := files) d)
              (offlineRowsAt (files := files) d offlineProverCoinCounts (theSimulators (files := files) d) (theLetters (files := files) d))) ∧
          PrivateStopsAtMost
            (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0) := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named files live
  obtain ⟨-, x₀, -, -⟩ := VerifiableInference.Compilation.someRequestIsServed_holds files scope hr
  exact ⟨d, hd, thePartsAt_ok hd, offlineSides_whole scope live,
    fun owed => offline_clauses_of_four_owed d live scope hd hs x₀ owed⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.theSimulators_eq
#print axioms AtPublicFiles.OfflineRows.theLetters_eq
#print axioms AtPublicFiles.OfflineRows.fourTestsOwed_of_owed
#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_four_owed
#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_four_owed_at_files
