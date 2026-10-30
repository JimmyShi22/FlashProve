-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

-- Mends of typing and elaboration, pack c60df67f; no statement turned by them but mem_weave's.
/-
E2E/OfflineRowsAtFiles.lean: the offline file's rows at the three public files: at thePartsAt
(E2E/KeyArgumentsAt.lean), which is T1's value.

  `thePartsAt_ok`, `offlineBook_eq`   the value and the book, unfolded under their premises
  `senderValue`, `parts_prover`   the value's senders; Parts.prover at thePartsAt is keyProver at them
  `senderValue_atAll`   they bear the sixteen places, in scope
  `offlineRowsAt`        the offline file's rows at a description: a function of the lists S and the
                         letters c: A SOCKET: IT PAYS NOTHING, AND NOBODY COUNTS IT
  `offlineRowsAt_prover`, `offline_ready_at_files`   what the rows and the value have

Conditional on `LookupsStated` (E2E/OfflineLaying.lean): the two lookups' parts state what the book has
for them; if that premise is false at the written book the statements over it are empty.
Every sentence that names the rows' simulators has to take `RowsCovered` (E2E/OfflineRows.lean): where a
list is short, a simulator that tells nothing stands there, and the session prints a constant. The
four letters of `c` are somebody's to fill: with True there `Good.exact` is asked at every state.
Nothing on any simulator or any property.
-/
import E2E.OfflineReady
import E2E.KeyArgumentsAt
import E2E.KeyThePartsFacts
import E2E.KeySeatAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open VerifiableInference.Desc (Place)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyValues (WitK withSendingsAndLookups matrixEntryOf multiplicitiesGroups faceAt keyBatt oneOf)
open AtPublicFiles.KeyValueHolds (atAll_value place_p12At)
open AtPublicFiles.KeyLay (withTests)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

variable {files : PublicFiles}

/-- At a description the value is the description's. -/
theorem thePartsAt_ok {d : OfflineDescription} (h : offlineDescription files = .ok d) :
    thePartsAt files = partsOfDescription d := by
  unfold thePartsAt
  rw [h]
  rfl

/-- At the written sizes the book is the written book. -/
theorem offlineBook_eq {K₀ : KeyPub} (hK : fullPub = some K₀) : offlineProverCoinCounts = keyBook K₀ := by
  unfold offlineProverCoinCounts
  rw [hK]

/-- **The offline prover's senders at a description**, with the four proximity tests. -/
abbrev senderValue (d : OfflineDescription) := 
  offlineValue (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles files).EncodingRandomness)
    (fixedKeyParts (faceAt d.source 0) (keyBatt d.source) matrixInput.dummy () () idleRecord)
    d.source d.numbers d.later matrixReader (tableCoins files) matrixInput.inRange
    matrixInput.dummy (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0

/-- **T1's prover at this value is `keyProver` at these senders.** -/
theorem parts_prover (d : OfflineDescription) :
    (partsOfDescription (files := files) d).prover d = keyProver (senderValue (files := files) d) :=
  rfl

/-- In scope they bear the sixteen places. -/
theorem senderValue_atAll {Z : PublicFiles} {d : OfflineDescription}
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) :
    (senderValue (files := files) d).AtAll := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  have hW : (OnBytes.linMessageW (oneOf d.source).lin).isSome = true := by
    rw [el]
    have h := shape_full.1
    cases hq : OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape with
    | none => rw [hq] at h; cases h
    | some w => rfl
  have hsp : (K14.planData (parKey d.source d.later)).S.sharedSplitNeeded = true := by
    have hpar : parKey d.source d.later = QK := par_sourced hs scope
    rw [hpar]
    exact shape_full.2.1
  exact atAll_value _ _ _ _ _ _ _ _ _ _ _ _ _ hW hsp (place_p12At _ _) (place_p12At _ _)

/-- **The offline file's rows at a description.** A function of S and c. -/
abbrev offlineRowsAt (d : OfflineDescription) (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Unit
      Unit Unit) :=
  offlineRows (keyFileDescription d.source d.numbers d.later) Bk (senderValue (files := files) d) S c

/-- Their prover is T1's. -/
theorem offlineRowsAt_prover (d : OfflineDescription) (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Unit
      Unit Unit) :
    (offlineRowsAt (files := files) d Bk S c).prover ((partsOfDescription d).prover d) =
      (partsOfDescription d).prover d :=
  offlineRows_prover _ _ _ S c

/-- **The public fields of `Owed` at the rows, and the test on the owners**, in scope at the written
book: what `exactAt_of_owedAt`'s twin at the offline file asks that reads no run: `plan`, `book`,
`places`, `seats` at the muted rows, and `owns`. -/
theorem offline_owed_public {Z : PublicFiles} {d : OfflineDescription}
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    (keyFileDescription d.source d.numbers d.later).planOk = true ∧
      (keyBook K₀).word (keyFileDescription d.source d.numbers d.later) = none ∧
      (keyFileDescription d.source d.numbers d.later).placesOk = true ∧
      (offlineRowsAt (files := files) d (keyBook K₀) S c).mute.seated = true ∧
      (offlineRowsAt (files := files) d (keyBook K₀) S c).owns = true := by
  have hA := senderValue_atAll (files := files) hs scope
  refine ⟨hs.named.plan, AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK,
    AtPublicFiles.KeyThread.placesOk_of_plan hs.named.plan, ?_, ?_⟩
  · rw [seated_mute]
    exact offlineRows_seated _ _ scope hs.named hA S c
  · exact offlineRows_owns _ hK hA (by show 0 < 2; omega) S _ c

/-- The named member of the range is in range. -/
theorem dummy_in_range : matrixInput.inRange matrixInput.dummy = true := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf
    (VerifiableInference.OnPublicFiles.Flat.matrixOf fullIn.dummy)).isSome = true
  rw [VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf fullIn.dummy)]
  rfl

/-- **THE STATEMENT AT THE FILES: at every coin, at every index in range and every instance, the
rounds of T1's offline prover are prepared**, where the public files' test says yes, in scope. -/
theorem offline_ready_at_files (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) :
    ∃ (d : OfflineDescription) (K₀ : KeyPub), offlineDescription files = .ok d ∧
      fullPub = some K₀ ∧ offlineProverCoinCounts = keyBook K₀ ∧
      (LookupsStated K₀ (senderValue (files := files) d) →
      ∀ (M : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst) (k : Coins (keyBook K₀)),
        matrixInput.inRange M = true →
        ∃ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
          ((partsOfDescription d).prover d) M rc x k = .ok R) := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named files live
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  refine ⟨d, K₀, hd, hK, offlineBook_eq hK, ?_⟩
  intro hL M rc x k hin
  exact offline_ready _ d.source d.numbers d.later _ _ _ _ _ _ _ hs scope hK hL M rc x k hin
    dummy_in_range (senderValue_atAll hs scope)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.offlineRowsAt_prover
#print axioms AtPublicFiles.OfflineRows.offline_owed_public
#print axioms AtPublicFiles.OfflineRows.offline_ready_at_files
