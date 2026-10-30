-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsAtFiles.lean: the field `runs` of `OwedRest` (E2E/OfflineClauses.lean), in its own text (`RunsText`,
E2E/OfflineRunsPremises.lean), at the public files, a description d of them, the offline file's book and the prover
of the muted rows. The sixteen places that have a prover's side are paid by the files named below.

  `sendings_play_at_files`      PAID: the premise at the three sendings' places (E2E/OfflineRunsSendingsAtKey.lean)
  `ranges_play_at_files`        PAID: at the test on the ranges (E2E/OfflineRunsRanges.lean)
  `shared_tests_play_at_files`  PAID: at the shared chain's two tests (E2E/OfflineRunsSharedTestsFields.lean)
  `others_at_files`             `KeyOthersPlay` (E2E/OfflineRunsKey.lean) from the premise at the last chain's test; the shared
                                chain's six by E2E/OfflineRunsSharedSixFields.lean
  `runs_text_of_others`         `RunsText` from `KeyOthersPlay` at every pair of inputs
  `own_test_plays_at_files`     PAID: at the last chain's test (E2E/OfflineRunsOwnField.lean)
  `runs_text_of_own`            `RunsText` from the premise at the last chain's test, at every input
  `runs_text_at_files`          **`RunsText`**, from the files' description, `KeySourced` and scope alone
  `threadsAtFiles`              the invariants of form as a member of `ThreadsP` (E2E/OfflineRunsThreads.lean), wherever
                                `ready` has returned

Calls alone. No acceptance is spent or shown: a run that returns may be one that the verifier rejects. Nothing
on any property.
-/
import E2E.OfflineRunsPremises
import E2E.OfflineRunsKey
import E2E.OfflineRunsSendingsAtKey
import E2E.OfflineRunsRanges
import E2E.OfflineRunsSharedTestsFields
import E2E.OfflineRunsSharedSixFields
import E2E.OfflineRunsOwnField
import E2E.OfflineRunsThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyBook (idxPlace msgPlace rngPlace wPlace pointPlace foldedPlace locPlace omegaPlace zetaPlace
  splitPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope)

variable {files : PublicFiles} (d : OfflineDescription)

/-- **PAID: the premise at the three sendings' places.** -/
theorem sendings_play_at_files (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) (Bk : ProverCoinCounts)
    (own : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst Unit) :
    PlaysAtFirst (keyFileDescription d.source d.numbers d.later) Bk (keyProver (senderValue (files := files) d))
        own idxPlace ∧
      PlaysAtFirst (keyFileDescription d.source d.numbers d.later) Bk
        (keyProver (senderValue (files := files) d)) own msgPlace ∧
      PlaysAtFirst (keyFileDescription d.source d.numbers d.later) Bk
        (keyProver (senderValue (files := files) d)) own wPlace :=
  sendings_plays_at_first hs scope Bk _ _ (senderValue_atAll hs scope).first rfl rfl rfl own

/-- **PAID: the premise at the test on the ranges** (E2E/OfflineRunsRanges.lean). -/
theorem ranges_play_at_files (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) (own : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst Unit) :
    PlaysAtFirst (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)) own rngPlace := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact ranges_test (offlineBook_eq hK) hK hs scope _ (senderValue_atAll hs scope).first rfl own

/-- **PAID: the premise at the shared chain's two tests** (E2E/OfflineRunsSharedTestsFields.lean). -/
theorem shared_tests_play_at_files (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) (common : Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) :
    PlaysAtShared (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (keyProver (senderValue (files := files) d)) common foldedTestPlace ∧
      PlaysAtShared (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (keyProver (senderValue (files := files) d)) common omegaTestPlace := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  rw [offlineBook_eq hK]
  exact ⟨testOnFoldedRow_at_value _ _ _ _ _ _ _ _ _ _ _ hs scope hK common,
    testOnOmega_at_value _ _ _ _ _ _ _ _ _ _ _ hs scope hK common⟩

/-- **PAID: the premise at the last chain's test** (E2E/OfflineRunsOwnField.lean). -/
theorem own_test_plays_at_files (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) (own : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst Unit) :
    PlaysAtSecond (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)) own ownTestPlace := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact ownTest_at_value _ _ _ _ _ _ _ _ _ _ _ _ _ hs scope hK (offlineBook_eq hK) own

/-- `KeyOthersPlay` from the last chain's test: twelve of its thirteen fields are paid. -/
theorem others_at_files (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) {own : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst Unit}
    (common : Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey)
    (hown : PlaysAtSecond (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)) own ownTestPlace) :
    KeyOthersPlay (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts (senderValue (files := files) d)
      own common := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := shared_six_fields hs scope offlineProverCoinCounts
    (senderValue (files := files) d) (senderValue_atAll hs scope) rfl common
  exact
    { indexMasks := (sendings_play_at_files d hs scope offlineProverCoinCounts own).1
      multiplicities := (sendings_play_at_files d hs scope offlineProverCoinCounts own).2.1
      rangesTest := ranges_play_at_files d hs scope own
      messageW := (sendings_play_at_files d hs scope offlineProverCoinCounts own).2.2
      linPoint := s1
      foldedRowSending := s2
      locColumns := s3
      omegaSending := s4
      linZeta := s5
      split := s6
      testOnFoldedRow := (shared_tests_play_at_files d hs scope common).1
      testOnOmega := (shared_tests_play_at_files d hs scope common).2
      ownTest := hown }

/-- **The field `runs`, in its own text, from `KeyOthersPlay`.** -/
theorem runs_text_of_others (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (hO : ∀ own common, KeyOthersPlay (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (senderValue (files := files) d) own common) :
    RunsText (files := files) d S c ((partsOfDescription d).prover d) :=
  runs_at_files d hd hs scope S c (runs_of_blocks _ _ _) fun _ _ _ _ R _ =>
    key_blocks_play hs scope offlineProverCoinCounts (senderValue_atAll hs scope) rfl rfl rfl R.own R.common
      (hO _ _)

/-- **The field `runs`, in its own text, from the last chain's test.** -/
theorem runs_text_of_own (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (hown : ∀ own, PlaysAtSecond (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)) own ownTestPlace) :
    RunsText (files := files) d S c ((partsOfDescription d).prover d) :=
  runs_text_of_others d hd hs scope S c fun own common => others_at_files d hs scope common (hown own)

/-- **THE FIELD `runs`, IN ITS OWN TEXT**: at the files' description, in scope: every run of the prover of the muted
rows returns, at every input in the relation, all coins of the offline file's book and all challenges that the
rounds can draw, outside the stops. No premise on any sub-protocol. -/
theorem runs_text_at_files (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    RunsText (files := files) d S c ((partsOfDescription d).prover d) :=
  runs_text_of_own d hd hs scope S c fun own => own_test_plays_at_files d hs scope own

/-- **The invariants of form as a member of `ThreadsP`, at the files**: wherever `ready` has returned. -/
def threadsAtFiles (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true) {w₀ : FullSizeMatrix}
    {rc : (protocolAtFiles files).EncodingRandomness} {x : AtPublicFiles.KeyFile.KeyInst} {k : Coins offlineProverCoinCounts}
    {R : Ready FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit}
    (hR : ready (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)) w₀ rc x k = .ok R) :
    ThreadsP (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)) w₀ rc x k R :=
  threadsOfBlocks hR (planOk_at_files d hs) (rootedAll_at_files d hs scope)
    (planServes_at_files d hd scope w₀ rc x k R hR)
    (key_blocks_play hs scope offlineProverCoinCounts (senderValue_atAll hs scope) rfl rfl rfl R.own R.common
      (others_at_files d hs scope R.common (own_test_plays_at_files d hs scope R.own)))

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.sendings_play_at_files
#print axioms AtPublicFiles.OfflineRows.ranges_play_at_files
#print axioms AtPublicFiles.OfflineRows.shared_tests_play_at_files
#print axioms AtPublicFiles.OfflineRows.others_at_files
#print axioms AtPublicFiles.OfflineRows.runs_text_of_others
#print axioms AtPublicFiles.OfflineRows.own_test_plays_at_files
#print axioms AtPublicFiles.OfflineRows.runs_text_of_own
#print axioms AtPublicFiles.OfflineRows.runs_text_at_files
#print axioms AtPublicFiles.OfflineRows.threadsAtFiles
