-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaOwedAtFiles.lean: WHAT THE FIELD owed ASKS AT THE ROW OF THE TEST ON G_omega, AT THE PUBLIC FILES: `OwedSharedAt d S c Rel H
omegaTestPlace` (E2E/OfflineRowsByPlace.lean), at the offline prover's own senders (`senderValue`, E2E/OfflineRowsAtFiles.lean) and the offline
book, FROM ONE NAMED SENTENCE AT EVERY RUN: `SayAtRun` (E2E/OfflineSayAtRun.lean).

  `omegaJobAtSenders`        the job that the senders lay at the place, before the guard
  `OmegaLetters`           what is asked of the letters at the place: the simulators' two are a job's; that job stands at the written
                           place, has its own table, and its state on entry is `stateAtOmega` at the senders' parameters over what the description's shared
                           list has in front of the test; the row's condition at a part follows from `OnOmegaKey`, its letter on
                           positions from `budBoth`
  `OmegaSaysAtRuns`        THE ONE PREMISE: `SayAtRun` at every run that the field owed speaks of
  `omega_owed_at_files`    the theorem

Limits. Conditional on `OmegaSaysAtRuns`: no value is shown to meet it; it reads the input and the carried coins: no later
law may take it as a hypothesis on a run and then speak of the coins as drawn anew. `OmegaLetters` is a premise on letters: that
a simulators' job of that form simulates anything is the field good's, not said here. Nothing on any property.
-/
import E2E.OfflineOmegaDoor
import E2E.OfflineRowsByPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.Term
open ProofFile.Honest.K12.Light (ManyJob plainMany budBoth OnOmegaKey sentOf stateAtOmega)
open OnBytes (TableKey)
open H2K.Member (piKOFull)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyLay (jobKO bsOf wtOf rdOf)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyValueHolds (place_p12At)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

variable {files : PublicFiles}

/-- **The job that the offline prover's senders lay at the test on G_omega**, before the guard. -/
abbrev omegaJobAtSenders (d : OfflineDescription) : ManyJob (Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) Unit :=
  jobKO (senderValue (files := files) d).send (H2U.proximityTestParametersAt foldedTestPlace d.later.U)
    (H2U.proximityTestParametersAt omegaTestPlace (d.later.O.getD d.later.U)) (bsOf (senderValue (files := files) d))
    (wtOf (senderValue (files := files) d)) (rdOf (senderValue (files := files) d))

/-- **What is asked of the letters at the place.** -/
structure OmegaLetters (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) (Js : SimJob TableKey) : Prop where
  simulators : S.testOnOmega = [firstSim Js, restSim Js]
  place : Js.p = piKOFull
  ownTable : Js.own = true
  state : Js.rec₀ = stateAtOmega (senderValue (files := files) d).send.P
    (sentOf (senderValue (files := files) d).send.P.S) (H2U.proximityTestParametersAt foldedTestPlace d.later.U)
    ((keyFileDescription d.source d.numbers d.later).shared.blocksInOrder.takeWhile (·.place != omegaTestPlace))
  atPart : ∀ u ca m front,
    OnOmegaKey Face.shared (omegaJobAtSenders (files := files) d).toRun.toTest Js 1 u ca m front →
      (c.shared omegaTestPlace).atPart u ca m front
  positions : ∀ n ds asks, budBoth Js n ds asks → (c.shared omegaTestPlace).positions n ds asks

/-- **THE ONE PREMISE**: the rows that the test takes in hold at the members' words, at every run that the field owed
speaks of. -/
def OmegaSaysAtRuns (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
    (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit) : Prop :=
  ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ r,
    ρ.due (keyFileDescription d.source d.numbers d.later) = true →
    silentAt (keyFileDescription d.source d.numbers d.later)
      ((offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.prover H) w₀ rc x ρ = none →
    runC (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      ((offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.prover H) w₀ rc x k ρ = .ok r →
    SayAtRun Empty (omegaJobAtSenders (files := files) d).toRun.toTest
      (plainMany (omegaJobAtSenders (files := files) d)) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        ((offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.prover H) w₀ rc x k ρ)

/-- **WHAT THE FIELD owed ASKS AT THE ROW OF THE TEST ON G_omega, FROM THE ONE PREMISE.** -/
theorem omega_owed_at_files (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
    (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (hkey : ∀ x, H.key x = x.key) (Js : SimJob TableKey)
    (T : OmegaLetters (files := files) d S c Js)
    (say : OmegaSaysAtRuns (files := files) d S c Rel H) :
    OwedSharedAt (files := files) d S c Rel H omegaTestPlace := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  have e : parKey d.source d.later = QK := par_sourced hs scope
  have hPl : d.later = PF := later_sourced hs scope
  intro w₀ rc x hrel k ρ r hρ hsil hrun
  exact omega_owed_of_say hs scope live hK (offlineBook_eq hK) (senderValue (files := files) d)
    (by
      show (parKey d.source d.later).S.sharedSplitNeeded = true
      rw [e]
      exact writtenShape_splits)
    (place_p12At _ _)
    (by
      show (⟨parKey d.source d.later, 0⟩ : ProofFile.Honest.K14.SendPub) = _
      rw [e])
    _ _ (by rw [hPl]) (by rw [hPl]) rfl S c H hkey Js T.simulators T.place T.ownTable
    (by
      rw [← e]
      exact T.state)
    T.atPart
    T.positions hρ hrun (say w₀ rc x hrel k ρ r hρ hsil hrun)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.omega_owed_at_files
