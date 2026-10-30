-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyThePartsFacts.lean: what thePartsAt is, in scope. The laws on the offline prover take these
three ties: its description is the one that the verifier's seat makes, its book is keyBook, its later
places are the written ones.

  offlineDescription_named   OfflineDescriptionNamed: from key_sourced, the five calls being one
  thePartsAt_senders         at a description, the senders are offlineSenders
  thePartsAt_book            the book is keyBook at fullPub's value
  later_written              in scope and live the later places are PF
  par_written, senders_send, senders_split   the shared parameter, in scope
  thePartsAt_send, thePartsAt_split, par_at_written   hs, hsp and e of acceptedS_at_key, at the value

Limits. The written sizes alone where scope stands. Nothing on any property.
-/
import E2E.KeyArgumentsAt
import E2E.KeyShapeSharedTies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifiableInference.Desc.Key (beforeSharedPoint)

variable {files : PublicFiles}

/-- **The offline description is the verifier's seat's.** -/
theorem offlineDescription_named (files : PublicFiles) : protocolDataWellFormed (asDescriptionFiles files) = true →
    ∃ description, offlineDescription files = .ok description ∧
      AtPublicFiles.AtFiles.KeySourced files description.source description.numbers description.later := by
  intro live
  obtain ⟨source, numbers, later, sourced⟩ := AtPublicFiles.AtFiles.key_sourced files live
  obtain ⟨read, made, h0, h1, h2, h3, h4⟩ := sourced.source
  refine ⟨⟨source, numbers, later⟩, ?_, sourced⟩
  unfold offlineDescription
  simp only [bind, Except.bind, h0, h1, h2, h3, h4, pure, Except.pure]

/-- At a description that the files make, in live files, that description is sourced. -/
theorem sourced_of_ok (live : protocolDataWellFormed (asDescriptionFiles files) = true) {description : OfflineDescription}
    (h : offlineDescription files = .ok description) :
    AtPublicFiles.AtFiles.KeySourced files description.source description.numbers description.later := by
  obtain ⟨d, hd, sourced⟩ := offlineDescription_named files live
  rw [h] at hd
  have e : description = d := Except.ok.inj hd
  rw [e]
  exact sourced

/-- **At a description the senders are offlineSenders.** -/
theorem thePartsAt_senders {description : OfflineDescription}
    (h : offlineDescription files = .ok description) :
    (thePartsAt files).senders = offlineSenders description := by
  show (match offlineDescription files with
    | .ok description => offlineSenders description
    | .error _ => fallbackSenders) = _
  rw [h]

/-- **The book is keyBook at fullPub's value.** -/
theorem thePartsAt_book {publicData : KeyPub} (h : fullPub = some publicData) :
    (thePartsAt files).book = keyBook publicData := by
  show offlineProverCoinCounts = _
  unfold offlineProverCoinCounts
  rw [h]

/-- **In scope and live the later places are the written ones.** -/
theorem later_written (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {description : OfflineDescription} (h : offlineDescription files = .ok description) :
    description.later = AtPublicFiles.AtFiles.Full.PF :=
  AtPublicFiles.AtFiles.Full.later_sourced (sourced_of_ok live h) scope

/-- **The shared parameter is the written one.** -/
theorem par_written (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {description : OfflineDescription} (h : offlineDescription files = .ok description) :
    AtPublicFiles.KeySharedThread.parKey description.source description.later = AtPublicFiles.AtFiles.Full.QK :=
  AtPublicFiles.AtFiles.Full.par_sourced (sourced_of_ok live h) scope

/-- The senders' parameter of the shared chain. -/
theorem senders_send (description : OfflineDescription) :
    (offlineSenders (files := files) description).send =
      ⟨AtPublicFiles.KeySharedThread.parKey description.source description.later, 0⟩ := rfl

/-- **The written shape splits.** -/
theorem written_splits : AtPublicFiles.AtFiles.Full.QK.S.sharedSplitNeeded = true := by decide +kernel

/-- **The senders' shape splits, in scope.** -/
theorem senders_split (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {description : OfflineDescription} (h : offlineDescription files = .ok description) :
    (ProofFile.Honest.K14.planData
      (AtPublicFiles.KeySharedThread.parKey description.source description.later)).S.sharedSplitNeeded =
      true := by
  show (AtPublicFiles.KeySharedThread.parKey description.source description.later).S.sharedSplitNeeded = true
  rw [par_written scope live h]
  exact written_splits

/-- **hs of acceptedS_at_key, at the value.** -/
theorem thePartsAt_send (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {description : OfflineDescription} (h : offlineDescription files = .ok description) :
    (thePartsAt files).senders.send =
      ⟨AtPublicFiles.KeySharedThread.parKey description.source AtPublicFiles.AtFiles.Full.PF, 0⟩ := by
  rw [thePartsAt_senders h, senders_send, later_written scope live h]

/-- **hsp of acceptedS_at_key, at the value.** -/
theorem thePartsAt_split (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {description : OfflineDescription} (h : offlineDescription files = .ok description) :
    (thePartsAt files).senders.lin.S.sharedSplitNeeded = true := by
  rw [thePartsAt_senders h]
  exact senders_split scope live h

/-- **e of acceptedS_at_key, at the value.** -/
theorem par_at_written (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {description : OfflineDescription} (h : offlineDescription files = .ok description) :
    AtPublicFiles.KeySharedThread.parKey description.source AtPublicFiles.AtFiles.Full.PF = AtPublicFiles.AtFiles.Full.QK := by
  have e := par_written scope live h
  rwa [later_written scope live h] at e

end AtPublicFiles.AtFiles.HonestTerm
