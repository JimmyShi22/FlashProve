-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRowsGathered.lean: the fields good and owed of OwedRest (E2E/OfflineClauses.lean), whole,
from their cuts row by row (E2E/OfflineRowsByPlace.lean): six rows of the first chain are paid
(E2E/OfflineFirstRowsAtFiles.lean), the ten others and the field runs are the named premises
TenRowsOwed.

  GoodWhole, OwedWhole        the two fields' texts, to the letter but for the relation, a letter Rel.
  rows_places                 in scope the muted rows stand at the sixteen places, chain by chain.
  goodWhole_of_rows           GoodWhole at the laid simulators and the laid letters, from TenRowsOwed.
  owedWhole_of_rows           OwedWhole there, from TenRowsOwed.

CONDITIONAL: TenRowsOwed is a premise here: tenRowsOwed_of_four (E2E/OfflineFourRowsLeft.lean) gives a member from FourRowsOwed. What is paid here is the gathering,
and the six rows by calls of first_rows_at_files and owed_first_six_at_files; their limits stand.
This file does not import E2E/OfflineClauses.lean: that GoodWhole and OwedWhole are that structure's
fields is shown in E2E/OfflineRowsJoin.lean. Nothing on any property.
-/
import E2E.OfflineRowsByPlace

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
open AtPublicFiles.KeyBook (idxPlace msgPlace lookPlace rngPlace battPlace wPlace pointPlace foldedPlace
  locPlace omegaPlace zetaPlace splitPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope)

variable {files : PublicFiles}

section Whole
variable (d : OfflineDescription) (S : OfflineSimulators)
  (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
    Unit Unit Unit)

/-- The field good of OwedRest. -/
def GoodWhole : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  (∀ L ∈ G.first, (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
      F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
  (∀ L ∈ G.shared, (L.withField 1 0 F.shared.blocksInOrder [] 0).goodAt (earlierOf F 1) .shared
      F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
  ∀ L ∈ G.second, ∀ base skip,
    (L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder base skip).goodAt (earlierOf F 2) .own
      F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃

/-- The field owed of OwedRest, at a relation. -/
def OwedWhole (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
    (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ r, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r →
    (∀ L ∈ G.first, L.owedAt F.first.blocksInOrder k 0
      (fun a => orRefused (midAtW F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called) ∧
    (∀ L ∈ G.shared, L.owedAt F.shared.blocksInOrder k 1
      (fun a => orRefused (midSharedAtW F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called) ∧
    ∀ L ∈ G.second, L.owedAt F.second.blocksInOrder k 2
      (fun a => orRefused (midAtW F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called

/-- **In scope the muted rows of the shared chain stand at its eight places, and the last chain's at
its one.** -/
theorem rows_places {Z : PublicFiles} (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) :
    (∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.shared,
      L.place ∈ [pointPlace, foldedPlace, locPlace, omegaPlace, zetaPlace, splitPlace,
        foldedTestPlace, omegaTestPlace]) ∧
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.second,
      L.place ∈ [ownTestPlace] := by
  obtain ⟨-, e₂, e₃⟩ := offlineRows_places (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
    (senderValue (files := files) d) S c (senderValue_atAll hs scope)
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    have hm : L₀.place ∈ (offlineRows (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (senderValue (files := files) d) S c).shared.map (·.place) := List.mem_map_of_mem h₀
    rw [e₂] at hm
    exact hm
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    have hm : L₀.place ∈ (offlineRows (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
        (senderValue (files := files) d) S c).second.map (·.place) := List.mem_map_of_mem h₀
    rw [e₃] at hm
    exact hm

end Whole

section Gathered
variable (d : OfflineDescription) (T : TheirSimulators)
  (t : TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit)
  (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
  (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit)

/-- **THE FIELD good, WHOLE, FROM THE TEN ROWS.** -/
theorem goodWhole_of_rows (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true)
    (ten : TenRowsOwed (files := files) d (laidSimulators (senderValue (files := files) d) T)
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) Rel H) :
    GoodWhole (files := files) d (laidSimulators (senderValue (files := files) d) T)
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) := by
  obtain ⟨p₂, p₃⟩ := rows_places (files := files) d
    (laidSimulators (senderValue (files := files) d) T)
    (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) hs scope
  unfold GoodWhole
  refine ⟨goodFirst_of (first_rows_at_files d hs scope T _ (laidConditions_positions _ _ t))
    ten.rangesTestGood, fun L hL => ?_, fun L hL => ?_⟩
  · have hm := p₂ L hL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h
    · exact ten.linPointGood L hL h
    · exact ten.foldedRowSendingGood L hL h
    · exact ten.locColumnsGood L hL h
    · exact ten.omegaSendingGood L hL h
    · exact ten.linZetaGood L hL h
    · exact ten.splitGood L hL h
    · exact ten.testOnFoldedRowGood L hL h
    · exact ten.testOnOmegaGood L hL h
  · have hm := p₃ L hL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact ten.ownTestGood L hL hm

/-- **THE FIELD owed, WHOLE, FROM THE TEN ROWS.** -/
theorem owedWhole_of_rows (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true)
    (ten : TenRowsOwed (files := files) d (laidSimulators (senderValue (files := files) d) T)
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) Rel H) :
    OwedWhole (files := files) d (laidSimulators (senderValue (files := files) d) T)
      (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) Rel H := by
  obtain ⟨p₂, p₃⟩ := rows_places (files := files) d
    (laidSimulators (senderValue (files := files) d) T)
    (laidConditions _ offlineProverCoinCounts (senderValue (files := files) d) t) hs scope
  intro w₀ rc x hR k ρ r hρ hq hr
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_⟩
  · by_cases h : L.place = rngPlace
    · exact ten.rangesTestOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact owed_first_six_at_files d hs scope (laidConditions_letters _ _ _ t) hρ hr L hL h
  · have hm := p₂ L hL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h
    · exact ten.linPointOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact ten.foldedRowSendingOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact ten.locColumnsOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact ten.omegaSendingOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact ten.linZetaOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact ten.splitOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact ten.testOnFoldedRowOwed w₀ rc x hR k ρ r hρ hq hr L hL h
    · exact ten.testOnOmegaOwed w₀ rc x hR k ρ r hρ hq hr L hL h
  · have hm := p₃ L hL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact ten.ownTestOwed w₀ rc x hR k ρ r hρ hq hr L hL hm

end Gathered

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.rows_places
#print axioms AtPublicFiles.OfflineRows.goodWhole_of_rows
#print axioms AtPublicFiles.OfflineRows.owedWhole_of_rows
