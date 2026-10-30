-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFourRowsLeft.lean: of the ten rows that E2E/OfflineRowsByPlace.lean leaves as named premises
(TenRowsOwed), six more are paid: the shared chain's own rounds and its two sendings (rows 8 to 13:
E2E/OfflineSharedSixAtValue.lean). What stays owed: the four proximity tests, and that the run returns.

  TestConditions        the letters of the four proximity tests' rows: LETTERS.
  withSharedSix         the ten letters: the six rows' own (ownLetters, foldedLetters, omegaLetters) and
                        the four.
  FourRowsOwed          nine named premises: good and owed at each of the four tests' rows, and runs.
  tenRowsOwed_of_four   TenRowsOwed from them, at the simulators laidSimulators K (k14Lists K T) and the
                        letters laidConditions … (withSharedSix K q), K the offline prover's own senders.

CONDITIONAL: FourRowsOwed is a premise here: fourRowsOwed_of_tests (E2E/OfflineClausesOfFourTests.lean) gives a member from FourTestsOwed. It stands in for four rows' proofs
and for the run's. The six rows are paid by calls of shared_six_good_at_laid and
shared_six_owed_at_value: their limits stand; the second reads the public files' test. Nothing on any
property.
-/
import E2E.OfflineRowsGathered
import E2E.OfflineSharedSixAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open VerifiableInference.Desc (FileDescription Place)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (rngPlace pointPlace foldedPlace locPlace omegaPlace zetaPlace splitPlace
  foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.KeyValueHolds (place_p12At)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

section Letters
variable {W₀ Rc X₀ X Wk : Type}

/-- **The letters of the four proximity tests' rows.** LETTERS. -/
structure TestConditions (Fx : FileDescription AtPublicFiles.KeyFile.KeyInst) (Bk : ProverCoinCounts) (W₀ Rc X₀ X : Type) where
  rangesTest : RowConditions Bk Fx.S₁ (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit)
    (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit) X AtPublicFiles.KeyFile.KeyInst
  testOnFoldedRow : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  testOnOmega : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  ownTest : RowConditions Bk Fx.S₃ (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit)
    (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit) X AtPublicFiles.KeyFile.KeyInst

/-- **The ten letters**: the shared chain's six rows' own, and the four. -/
def withSharedSix {Fx : FileDescription AtPublicFiles.KeyFile.KeyInst} {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc X₀ X Wk)
    (q : TestConditions Fx Bk W₀ Rc X₀ X) : TheirConditions Fx Bk W₀ Rc X₀ X where
  rangesTest := q.rangesTest
  linPoint := ownLetters
  foldedRowSending := foldedLetters K
  locColumns := ownLetters
  omegaSending := omegaLetters K
  linZeta := ownLetters
  split := ownLetters
  testOnFoldedRow := q.testOnFoldedRow
  testOnOmega := q.testOnOmega
  ownTest := q.ownTest

end Letters

variable {files : PublicFiles}

/-- **WHAT STAYS OWED WHEN TWELVE ROWS ARE PAID**: good and owed at each of the four proximity tests'
rows, at its own place, and the field runs. NAMED PREMISES. fourRowsOwed_of_tests (E2E/OfflineClausesOfFourTests.lean) gives a member from FourTestsOwed. -/
structure FourRowsOwed (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
    (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit) : Prop where
  rangesTestGood : GoodFirstAt (files := files) d S c rngPlace
  testOnFoldedRowGood : GoodSharedAt (files := files) d S c foldedTestPlace
  testOnOmegaGood : GoodSharedAt (files := files) d S c omegaTestPlace
  ownTestGood : GoodLastAt (files := files) d S c ownTestPlace
  runs : RunsAt (files := files) d S c Rel H
  rangesTestOwed : OwedFirstAt (files := files) d S c Rel H rngPlace
  testOnFoldedRowOwed : OwedSharedAt (files := files) d S c Rel H foldedTestPlace
  testOnOmegaOwed : OwedSharedAt (files := files) d S c Rel H omegaTestPlace
  ownTestOwed : OwedLastAt (files := files) d S c Rel H ownTestPlace

section Paid
variable (d : OfflineDescription) (T : TheirSimulators)
  (q : TestConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit)
  (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
  (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit)

/-- At the laid letters the six rows' letters are their own. -/
theorem laidConditions_sharedSix :
    SharedSixLetters (senderValue (files := files) d)
      (laidConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (senderValue (files := files) d) (withSharedSix (senderValue (files := files) d) q)) :=
  sharedSixLetters_of _ _ rfl rfl rfl rfl rfl rfl

/-- The field good at the six rows, at the files. -/
theorem shared_six_good_at_files (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) :
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts
        (laidSimulators (senderValue (files := files) d)
          (k14Lists (senderValue (files := files) d) T))
        (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
          (withSharedSix (senderValue (files := files) d) q))).mute.shared,
      SixPlace L.place →
      (L.withField 1 0 (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription d.source d.numbers d.later) 1) .shared
        (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder
        (orderOf (keyFileDescription d.source d.numbers d.later)) 1 0
        (offlineRowsAt (files := files) d offlineProverCoinCounts
          (laidSimulators (senderValue (files := files) d)
            (k14Lists (senderValue (files := files) d) T))
          (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
            (withSharedSix (senderValue (files := files) d) q))).mute.falls₂ := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact shared_six_good_at_laid _ d.source d.numbers d.later _ _ _ _ _ _ _ _ 0 hs scope hK
    (offlineBook_eq hK) (place_p12At _ _) (place_p12At _ _) T _ (laidConditions_sharedSix d q)

/-- **TenRowsOwed FROM THE FOUR TESTS' ROWS.** -/
theorem tenRowsOwed_of_four (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (four : FourRowsOwed (files := files) d
      (laidSimulators (senderValue (files := files) d)
        (k14Lists (senderValue (files := files) d) T))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
        (withSharedSix (senderValue (files := files) d) q)) Rel H) :
    TenRowsOwed (files := files) d
      (laidSimulators (senderValue (files := files) d)
        (k14Lists (senderValue (files := files) d) T))
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
        (withSharedSix (senderValue (files := files) d) q)) Rel H := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  have good := shared_six_good_at_files d T q hs scope
  have owed : ∀ w₀ rc x (k : Coins offlineProverCoinCounts) ρ r,
      ρ.due (keyFileDescription d.source d.numbers d.later) = true →
      runC (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        ((offlineRowsAt (files := files) d offlineProverCoinCounts
          (laidSimulators (senderValue (files := files) d)
            (k14Lists (senderValue (files := files) d) T))
          (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d)
            (withSharedSix (senderValue (files := files) d) q))).mute.prover H) w₀ rc x k ρ =
        .ok r → _ := fun w₀ rc x k ρ r hρ h =>
    shared_six_owed_at_value _ d.source d.numbers d.later _ _ _ _ _ _ _ _ 0 hs scope live hK
      (offlineBook_eq hK) (place_p12At _ _) (place_p12At _ _) _
      (simsAtSix_laid (senderValue (files := files) d) T) _ (laidConditions_sharedSix d q) H w₀ rc
      x k ρ r hρ h
  exact
    { rangesTestGood := four.rangesTestGood
      linPointGood := fun L hL e => good L hL (Or.inl e)
      foldedRowSendingGood := fun L hL e => good L hL (Or.inr (Or.inl e))
      locColumnsGood := fun L hL e => good L hL (Or.inr (Or.inr (Or.inl e)))
      omegaSendingGood := fun L hL e => good L hL (Or.inr (Or.inr (Or.inr (Or.inl e))))
      linZetaGood := fun L hL e => good L hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      splitGood := fun L hL e => good L hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
      testOnFoldedRowGood := four.testOnFoldedRowGood
      testOnOmegaGood := four.testOnOmegaGood
      ownTestGood := four.ownTestGood
      runs := four.runs
      rangesTestOwed := four.rangesTestOwed
      linPointOwed := fun w₀ rc x _ k ρ r hρ _ h L hL e => owed w₀ rc x k ρ r hρ h L hL (Or.inl e)
      foldedRowSendingOwed := fun w₀ rc x _ k ρ r hρ _ h L hL e =>
        owed w₀ rc x k ρ r hρ h L hL (Or.inr (Or.inl e))
      locColumnsOwed := fun w₀ rc x _ k ρ r hρ _ h L hL e =>
        owed w₀ rc x k ρ r hρ h L hL (Or.inr (Or.inr (Or.inl e)))
      omegaSendingOwed := fun w₀ rc x _ k ρ r hρ _ h L hL e =>
        owed w₀ rc x k ρ r hρ h L hL (Or.inr (Or.inr (Or.inr (Or.inl e))))
      linZetaOwed := fun w₀ rc x _ k ρ r hρ _ h L hL e =>
        owed w₀ rc x k ρ r hρ h L hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      splitOwed := fun w₀ rc x _ k ρ r hρ _ h L hL e =>
        owed w₀ rc x k ρ r hρ h L hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
      testOnFoldedRowOwed := four.testOnFoldedRowOwed
      testOnOmegaOwed := four.testOnOmegaOwed
      ownTestOwed := four.ownTestOwed }

end Paid

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.laidConditions_sharedSix
#print axioms AtPublicFiles.OfflineRows.shared_six_good_at_files
#print axioms AtPublicFiles.OfflineRows.tenRowsOwed_of_four
