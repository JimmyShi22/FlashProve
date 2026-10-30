-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsPremises.lean: for "every run returns" at the key file (the field runs of OwedRest,
E2E/OfflineClauses.lean): THE PREMISES THAT ARE NO SUB-PROTOCOL's, at the public files, a description d of
them, the offline file's book (offlineProverCoinCounts) and the prover of the muted rows; and that field's text
from them, from the law RunsOfBlocks and from BlocksPlay (E2E/OfflineRunsForm.lean).

  prover_at_files        the prover of the muted rows, at the value's prover (partsOfDescription d).prover d,
                         is keyProver (senderValue d)
  lookupsStated_at_files the premise LookupsStated of offline_ready (E2E/OfflineReady.lean), at senderValue d
  ready_at_files         (i) ready returns: at every index in range, all the committer's coins, every
                         instance and ALL COINS of the book offlineProverCoinCounts
  sealPlain_at_files     (ii) the first chain's sealing round is plain
  planOk_at_files, rootedAll_at_files   the two public tests beside it
  planServes_at_files    (iii) where ready has returned, the plan serves the rounds
  inRange_of_relation    where the relation of Owed at the key file holds (the text of KeyRel,
                         E2E/OfflineClauses.lean), the index is in the prover's range
  RunsText d S c H       the field runs of OwedRest, its text to the letter, with KeyRel and its wrK
                         (an abbreviation of E2E/KeyExact.lean) written out
  runs_at_files          RunsText at the value's prover, from RunsOfBlocks and BlocksPlay at
                         keyProver (senderValue d)

By what. (i) offline_ready (E2E/OfflineReady.lean), its premise had from lookupsStated_offline
(E2E/LotLookupsStated.lean), which calls lookupRowStatesWhatTheKeyBookHas
(E2E/Lookup/Key/LookupSidePaysAtTheKeyBook.lean). (ii) sealPlain_key (E2E/KeyAcceptAtFiles.lean), at every
description. (iii) lotPlanServes (E2E/LotPlanServes.lean). rootedAll_key (E2E/KeyValueHolds.lean);
inRange_iff (E2E/KeyRangeOne.lean). Calls alone.

Premises: KeySourced at the files, scope; for (iii) that d is the files' description.
Limits. ready says that the rounds are prepared: no round has been played. RunsOfBlocks and BlocksPlay are
PREMISES of runs_at_files: the first is the statement of E2E/OfflineRunsForm.lean, the second asks one sentence
of each sub-protocol; neither is shown here, so the field runs is not shown here. This file does not import
E2E/OfflineClauses.lean: that RunsText is that field's text is seen by holding the two side by side, not by
Lean. Nothing on any property.
-/
import E2E.OfflineRowsAtFiles
import E2E.OfflineRunsForm
import E2E.LotLookupsStated
import E2E.LotPlanServes
import E2E.KeyAcceptAtFiles
import E2E.KeyRangeOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open LPFD.Full (XF)
open OnBytes.Flat (RecFull)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope)

local instance (priority := high) runsPremisesPads : Nonempty PadZ :=
  AtPublicFiles.Committed.pads_nonempty frS 402653181

variable {files : PublicFiles} (d : OfflineDescription)

/-- **The prover of the muted rows is the value's.** -/
theorem prover_at_files (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    (offlineRowsAt (files := files) d Bk S c).mute.prover ((partsOfDescription d).prover d) =
      keyProver (senderValue (files := files) d) := by
  rw [prover_mute, offlineRowsAt_prover]
  rfl

/-- **The two lookups' parts state what the written book has for them.** -/
theorem lookupsStated_at_files {Z : PublicFiles} (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀) :
    LookupsStated K₀ (senderValue (files := files) d) :=
  Lots.lookupsStated_offline _ d.source d.numbers d.later _ _ _ _ _ _ _ hs scope hK

/-- ready returns at any book that is the written one. -/
theorem ready_at_book {Z : PublicFiles} (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts}
    (hB : Bk = keyBook K₀) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst) (k : Coins Bk)
    (hin : matrixInput.inRange w₀ = true) :
    ∃ R, ready (keyFileDescription d.source d.numbers d.later) Bk (keyProver (senderValue (files := files) d))
      w₀ rc x k = .ok R := by
  subst hB
  exact offline_ready _ d.source d.numbers d.later _ _ _ _ _ _ _ hs scope hK
    (lookupsStated_at_files d hs scope hK) w₀ rc x k hin dummy_in_range (senderValue_atAll hs scope)

/-- **(i) ready returns**, at the offline file's book. -/
theorem ready_at_files {Z : PublicFiles} (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst)
    (k : Coins offlineProverCoinCounts) (hin : matrixInput.inRange w₀ = true) :
    ∃ R, ready (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)) w₀ rc x k = .ok R := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact ready_at_book d hs scope hK (offlineBook_eq hK) w₀ rc x k hin

/-- **(ii) The sealing round is plain.** -/
theorem sealPlain_at_files : sealPlain (keyFileDescription d.source d.numbers d.later) = true :=
  sealPlain_key _ _ _

/-- The description passes its tests on the plan. -/
theorem planOk_at_files {Z : PublicFiles} (hs : KeySourced Z d.source d.numbers d.later) :
    (keyFileDescription d.source d.numbers d.later).planOk = true := hs.named.plan

/-- Every sub-protocol that declares a root has a prover's side. -/
theorem rootedAll_at_files {Z : PublicFiles} (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) :
    rootedAll (keyFileDescription d.source d.numbers d.later) (keyProver (senderValue (files := files) d)) =
      true :=
  AtPublicFiles.KeyValueHolds.rootedAll_key scope hs.named _ (senderValue_atAll hs scope)

/-- **(iii) Where ready has returned, the plan serves the rounds.** -/
theorem planServes_at_files (hd : offlineDescription files = .ok d) (scope : InScope files = true)
    {Bk : ProverCoinCounts} (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst) (k : Coins Bk)
    (R : Ready FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit)
    (hR : ready (keyFileDescription d.source d.numbers d.later) Bk (keyProver (senderValue (files := files) d))
      w₀ rc x k = .ok R) :
    PlanServes (keyProver (senderValue (files := files) d)) w₀ rc R :=
  AtPublicFiles.AtFiles.HonestTerm.Lots.lotPlanServes hd scope w₀ rc x k R hR

/-- **Where the relation of Owed at the key file holds, the index is in the prover's range.** -/
theorem inRange_of_relation (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst)
    (h : relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i (_ : XF) => inRange i)
      (fun a : XF × RecFull => keyInstanceOfOutOfDomainSample a.2) w₀ rc x) :
    matrixInput.inRange w₀ = true := by
  obtain ⟨s, x', -, hr⟩ := h
  exact (AtPublicFiles.AtFiles.HonestTerm.inRange_iff w₀).2 hr

/-- **The field runs of OwedRest**, with the relation written out. -/
def RunsText (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ w₀ rc x, relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i (_ : XF) => inRange i)
      (fun a : XF × RecFull => keyInstanceOfOutOfDomainSample a.2) w₀ rc x →
    ∀ (k : Coins offlineProverCoinCounts) ρ, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    ∃ r, runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r

/-- **The field from the law and the sub-protocols.** -/
theorem runs_at_files (hd : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (law : RunsOfBlocks (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (keyProver (senderValue (files := files) d)))
    (blocks : ∀ (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst) (k : Coins offlineProverCoinCounts) R,
      ready (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (keyProver (senderValue (files := files) d)) w₀ rc x k = .ok R →
      BlocksPlay (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (keyProver (senderValue (files := files) d)) R.own R.common) :
    RunsText (files := files) d S c ((partsOfDescription d).prover d) := by
  unfold RunsText
  intro F G w₀ rc x hrel k ρ hρ hq
  have e : G.prover ((partsOfDescription d).prover d) = keyProver (senderValue (files := files) d) :=
    prover_at_files d offlineProverCoinCounts S c
  rw [e] at hq ⊢
  obtain ⟨R, hR⟩ := ready_at_files d hs scope w₀ rc x k (inRange_of_relation w₀ rc x hrel)
  exact law w₀ rc x k ρ R hR (planOk_at_files d hs) (sealPlain_at_files d)
    (rootedAll_at_files d hs scope) (planServes_at_files d hd scope w₀ rc x k R hR)
    (blocks w₀ rc x k R hR) hρ hq

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.prover_at_files
#print axioms AtPublicFiles.OfflineRows.lookupsStated_at_files
#print axioms AtPublicFiles.OfflineRows.ready_at_files
#print axioms AtPublicFiles.OfflineRows.sealPlain_at_files
#print axioms AtPublicFiles.OfflineRows.rootedAll_at_files
#print axioms AtPublicFiles.OfflineRows.planServes_at_files
#print axioms AtPublicFiles.OfflineRows.inRange_of_relation
#print axioms AtPublicFiles.OfflineRows.runs_at_files
