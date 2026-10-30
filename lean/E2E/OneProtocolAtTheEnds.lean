-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OneProtocolAtTheEnds.lean: WHAT IS PROVED OF THE OFFLINE PART, OF ONE PROTOCOL AND ONE PROVER, IN ONE BUILD. Soundness as an interactive oracle proof (all three
verifiers), the offline clause of completeness and the offline lines of zero knowledge, each a THEOREM called here by name, at
ONE bound protocol, ONE bound offline prover and ONE bound value of the offline proof-of-work bits. A bridge: it states no goal and turns
none.

  `OfflineAtOneProtocol L H work …`   the three side by side, general: L, H : an honest prover of L's offline part, and work are bound once
  `offline_at_one_protocol`   **it holds** at L := `protocolAtFiles Z`, H := `offlineProver (thePartsAt Z)`, work := `(workAtFiles Z).offline`: for public files in
                        scope, read, where the files' own test says yes
  `honest_offline_run_in_soundness_words`   THE CALL: the honest offline prover's own run, at challenges cleared by soundness's own clearing, laid
                        as the offline part of soundness's whole run at the honest table and its own sample, meets the first
                        clause of `WholeRun.Accepted`
  `extractor_answers_at_the_files`   THE CALL THAT SPENDS BOTH: by the theorem of soundness AND the offline end of completeness: soundness's extractor answers on
                        the honest table with its own sample (E2E/ExtractorAnswersOnHonestTables.lean)
  `one_index_one_relation_at_the_files`   at a served request, on the honest table with its own sample: the extractor returns THE HONEST INDEX, no
                        collision, and the request lies in soundness's relation (E2E/OneIndexOneRelation.lean), the clause of soundness supplied
  `offline_at_the_written_files`   A TEST OF EMPTINESS: at the written public files the three premises are theorems

WHICH THEOREMS ARE CALLED. Soundness: `soundAsIOPAtTheProtocol` (E2E/SoundAsIOPAtFilesProofs.lean). Completeness, offline:
`offlineDebts_at_the_files` (E2E/LotKeyAcceptsAtTheFiles.lean) through `offlineClause_of_debts` (E2E/CompleteAsIOPOffline.lean). Zero knowledge,
offline: `offline_clauses_at_the_files` (E2E/OfflineClausesAtTheFiles.lean). That the prover of the second is the prover of the third:
`offline_prover_at_description` (E2E/ThreeAtOneProtocol.lean).

WHAT ONE BUILD BUYS. Where this file and all that it imports are compiled together from their sources, the three theorems stand over one compiled
library: the name `protocolAtFiles Z` has one meaning beneath all three.

HOW TO READ THE CLAUSES. (1) offlineComplete is the offline field of the definition of completeness in parts (`CompleteInParts.offlineAccepted`,
Johnson/Face/CompleteAsIOP.lean), at error 0; faithful is the offline third of its clause on the work bits. (2) offlineZeroKnowledge is the fields offline and offlineStops,
and speaksOfItsTable the offline third of the field tables, of `RunByRun` (VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean), which is the field runByRun of
`HonestVerifierZeroKnowledge`; faithful is the offline third of its field faithful. Its other fields (link, online, their stops, refuses; twoIndices; wholeView) are not touched
here. (3) THE NUMBERS STAND OVER DIFFERENT LAWS AND ARE NOT TO BE COMPARED: 2^-128 is a
share of ALL of one round's challenges, the bits of proof of work among them; the 0 of offlineComplete is over the prover's coins and the challenges
that pass. (4) IN THIS STRUCTURE ZERO KNOWLEDGE's DOMAIN IS THE WIDER: every matrix in range; offlineComplete speaks at the indices of served requests alone, and not every
matrix in range serves a request. That the offline run is accepted at EVERY matrix in range, so that the run of which the simulator is exact is an accepted run
over that whole domain: this file says nothing of it.

WHERE IT HOLDS. At public files in scope, read, where the files' own test says yes. The written full-size example is one such
(`offline_at_the_written_files`); no theorem ties it to a file on a disk.

Limits. THE OFFLINE PART ALONE of completeness and of zero knowledge: nothing on the link's or the online prover: NEITHER PROPERTY IS PROVED FOR THE PROTOCOL
HERE. Before hashing: nothing on the compiled prover and verifier. The prover is the one written in Lean, at the key file's description: no
program. The limits of the three theorems that are called stand, each in its own file. In scope, at the written book.
-/
import E2E.ThreeAtOneProtocol
import E2E.OfflineAcceptedInSoundnessWords
import E2E.ExtractorAnswersOnHonestTables
import E2E.OneIndexOneRelation
import E2E.SoundAsIOPAtFilesProofs
import E2E.LotKeyAcceptsAtTheFiles
import E2E.OfflineClausesAtTheFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.OneProtocol
open Iop
open VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed (PadZ pads_nonempty)
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles InScope asDescriptionFiles storedPublicFiles)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open _root_.Compile.Lifetime (SimOf)
open AtPublicFiles.OfflineRows (offline_clauses_at_the_files)
open AtFullSide.Honest.TheKeyLetters (offlineDebts_at_the_files)

local instance (priority := high) atTheEndsPads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) atTheEndsRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) atTheEndsRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

/-- **SOUNDNESS, AND THE OFFLINE PARTS OF COMPLETENESS AND ZERO KNOWLEDGE, AT ONE BOUND PROTOCOL, ONE BOUND OFFLINE PROVER AND ONE BOUND VALUE OF ITS WORK BITS.** -/
structure OfflineAtOneProtocol {Index Request : Type} (L : HolographicProtocol Index Request)
    (H : Honest L.offline (Index × L.EncodingRandomness × L.OutOfDomainSeed)) (work : WorkBits L.offline.shape)
    (served wide : Index → Request → Prop) (inRange : Index → Prop)
    (offlineMarks : RoundSplits L.offline.shape) (offlinePlaces : ℕ) (linkMarks : RoundSplits L.link.shape)
    (linkPlaces : ℕ) (roundBound : ℝ≥0∞) : Prop where
  /-- round-by-round knowledge soundness for the index, of L's three verifiers -/
  sound : L.IndexKnowledgeSoundIOP wide offlineMarks offlinePlaces linkMarks linkPlaces roundBound
  /-- the work bits are L's offline verifier's own -/
  faithful : WorkBitsFaithful L.offline work
  /-- H speaks of the encoding of its own index -/
  speaksOfItsTable : ∀ i r e, H.ext (i, r, e) = L.encodeIndex i r
  /-- completeness, offline: at the index of a served request, H's run against L's offline verifier fails with chance 0, over H's coins and the challenges that pass the work bits -/
  offlineComplete : ∀ i x r e, served i x → FailsRarely H work (L.encodeIndex i r) (i, r, e) (L.recOf i r e) 0
  /-- honest-verifier zero knowledge, offline, at indices in range: a simulator of L's offline part, exact at cleared challenges outside H's private stops, which have chance 0 -/
  offlineZeroKnowledge : ∃ simulator : SimOf L.offline,
    ExactOutsideStops H (fun w y => inRange w.1 ∧ L.validT w y) work.cleared simulator ∧
      PrivateStopsAtMost H (fun w y => inRange w.1 ∧ L.validT w y) work 0

variable {Z : PublicFiles}

/-- **IT HOLDS, AT `protocolAtFiles Z` AND THE PROTOCOL's OFFLINE HONEST PROVER.** -/
theorem offline_at_one_protocol (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    OfflineAtOneProtocol (protocolAtFiles Z) (offlineProver (thePartsAt Z)) (workAtFiles Z).offline
      (ServedRequest committerCoinCountLessOne Z hr) (relationAtFiles Z) rangeAtFiles (filesAt Z).annT (offlinePlaces Z)
      (filesAt Z).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨d, hd, -, -, speaks, exact, stops⟩ := offline_clauses_at_the_files live scope hr
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  obtain ⟨Tied, TiedM, D⟩ := offlineDebts_at_the_files hr hd scope live hK₀
  refine ⟨soundAsIOPAtTheProtocol Z pp scope hr live, (workFaithful_atFiles Z).offline, speaks, ?_,
    ⟨_, exact, stops⟩⟩
  intro i x r e hy
  rw [offline_prover_at_description (thePartsAt Z) hd]
  have h := offlineClause_of_debts (workFaithful_atFiles Z) D i x r e hy
  simpa using h

/-- **THE CALL**: at a served request, at cleared challenges, the honest offline run is accepted. -/
theorem honest_offline_run_in_soundness_words (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (i : FullSizeMatrix) (x : LPFD.Full.XF)
    (hy : ServedRequest committerCoinCountLessOne Z hr i x) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed)
    (c : (offlineProver (thePartsAt Z)).Coin) (ρ : Rho (protocolAtFiles Z).offline.shape) (run : (protocolAtFiles Z).WholeRun)
    (hT : run.firstTable = (protocolAtFiles Z).encodeIndex i r) (hS : run.firstSample = (protocolAtFiles Z).recOf i r e)
    (hO : run.offline = (((offlineProver (thePartsAt Z)).strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run
      ((offlineClearing Z).cleared ρ)).1) :
    (protocolAtFiles Z).offline.accept run.firstSample run.firstTable run.offline = true := by
  obtain ⟨d, hd⟩ := AtPublicFiles.FirstH.Lots.described_of_live Z live
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  obtain ⟨Tied, TiedM, D⟩ := offlineDebts_at_the_files hr hd scope live hK₀
  have e0 := offline_prover_at_description (thePartsAt Z) hd
  revert c
  rw [e0]
  intro c hO
  exact offline_part_of_whole_run D i x r e hy c ρ run hT hS hO

/-- **THE CALL THAT SPENDS BOTH THEOREMS ON ONE OBJECT**: soundness's extractor answers on the honest table with its own sample, where that table has no
collision at the sample's point: by the theorem of soundness and the offline end of completeness together. -/
theorem extractor_answers_at_the_files (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (i : FullSizeMatrix) (x : LPFD.Full.XF)
    (hy : ServedRequest committerCoinCountLessOne Z hr i x) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed)
    (hc : ¬ (protocolAtFiles Z).hasCollisionAt ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e).1) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) ≠ none := by
  obtain ⟨errors, within, sound⟩ := soundAsIOPAtTheProtocol Z pp scope hr live
  obtain ⟨d, hd⟩ := AtPublicFiles.FirstH.Lots.described_of_live Z live
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  obtain ⟨Tied, TiedM, D⟩ := offlineDebts_at_the_files hr hd scope live hK₀
  exact extractor_answers within sound D i x hy r e hc

/-- **ONE INDEX, NESTED RELATIONS, WITH NO PREMISE BUT ON THE PUBLIC FILES**: at a served request, on the honest table with its own sample: soundness's extractor
returns the honest index, the table has no collision there, and the request lies in the relation at which soundness concludes. -/
theorem one_index_one_relation_at_the_files (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (i : FullSizeMatrix) (x : LPFD.Full.XF)
    (hy : ServedRequest committerCoinCountLessOne Z hr i x) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i ∧
      ¬ (protocolAtFiles Z).hasCollisionAt ((protocolAtFiles Z).encodeIndex i r) e ∧ relationAtFiles Z i x := by
  obtain ⟨errors, -, sound⟩ := soundAsIOPAtTheProtocol Z pp scope hr live
  exact one_index_one_relation sound scope i x hy r e

/-- **A TEST OF EMPTINESS: AT THE WRITTEN PUBLIC FILES** the three premises are theorems. -/
theorem offline_at_the_written_files :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles storedPublicFiles = .ok pp),
      OfflineAtOneProtocol (protocolAtFiles storedPublicFiles) (offlineProver (thePartsAt storedPublicFiles)) (workAtFiles storedPublicFiles).offline
        (ServedRequest committerCoinCountLessOne storedPublicFiles hr) (relationAtFiles storedPublicFiles) rangeAtFiles (filesAt storedPublicFiles).annT
        (offlinePlaces storedPublicFiles) (filesAt storedPublicFiles).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨pp, hr⟩ := AtFullSide.Honest.TheKeyLetters.read_zFull
  exact ⟨pp, hr, offline_at_one_protocol VerifierAndGoals.inScope_full hr AtFullSide.Top.theLive_zFull⟩

end AtPublicFiles.OneProtocol

#print axioms AtPublicFiles.OneProtocol.offline_at_one_protocol
#print axioms AtPublicFiles.OneProtocol.honest_offline_run_in_soundness_words
#print axioms AtPublicFiles.OneProtocol.extractor_answers_at_the_files
#print axioms AtPublicFiles.OneProtocol.one_index_one_relation_at_the_files
#print axioms AtPublicFiles.OneProtocol.offline_at_the_written_files
