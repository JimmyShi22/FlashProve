-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/OfflineClauses.lean: T3's offline clauses at the offline prover's own value: index privacy's
rung (E2E/KeyExact.lean; Johnson/T3/OfflineAtTheTerm.lean) with what it asks paid at that value, as
far as it goes.

  `isProvK_at`     `IsProvK` at T1's prover of the value, at the rows `offlineRowsAt`
  `quiet_at`       `NoSecondStop` there
  `input_at`       the field `input` of `Owed`, at the relation `relAt` of the index's range
  `OwedRest`       the three fields of `Owed` that stay owed: `good`, `runs`, `owed`: LETTERS
  `owed_of_rest`   `Owed` at the key's rows from these three
  `offline_clauses`   T3's three offline lines, with `OwedRest` as their one premise on the rows

CONDITIONAL: `OwedRest` is a premise: no member of it is known. The rows' simulators are a letter S
and their conditions a letter c: this file pays nothing on them, and `RowsCovered` is not asked
here because Lean does not see it; whoever fills `OwedRest` has it in `good`. Nothing here proves zero
knowledge of any protocol.
-/
import E2E.OfflineRowsAtFiles
import E2E.KeyExact
import E2E.KeyStoredAtValue
import E2E.KeyRangeOne
import E2E.KeyThePartsFacts
import Johnson.T3.OfflineAtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput tableCoins)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open LPFD.Full (XF)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.KeyValueHolds (noSecond_value)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm ProofFile.Honest.Term
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open VerifiableInference.Compilation
open P5J

local instance (priority := high) instOfflineClauses0 : Nonempty PadZ := pads_nonempty frS 402653181

variable {files : PublicFiles}

/-- The relation of `Owed` at the key file: the index is in range. -/
abbrev KeyRel (files : PublicFiles) := relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i (_ : XF) => inRange i) wrK

section Value
variable (d : OfflineDescription) (S : OfflineSimulators)
  (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
    Unit Unit Unit)

/-- **T1's prover at the value is the prover of the rows, with the committer's key and columns.** -/
theorem isProvK_at (hk : d.source.chains.made.sized.key = Lk6.AtPlan.keyFull) :
    IsProvK files (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      (offlineRowsAt (files := files) d offlineProverCoinCounts S c) ((partsOfDescription d).prover d) where
  key := rfl
  stored := fun w rc it x => stored_at_description d hk w rc it x
  first := offlineSides_first _ _ _ _ _ _ _ _
  shared := offlineSides_shared _ _ _ _ _ _ _ _
  second := offlineSides_second _ _ _ _ _ _ _ _

/-- **No part of the first or the last chain has a stop that reads the private input.** -/
theorem quiet_at : AtPublicFiles.Stops.NoSecondStop ((partsOfDescription (files := files) d).prover d) :=
  noSecond_value _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **What stays owed of `Owed` at the rows.** Three fields as `Owed` has them. LETTERS. -/
structure OwedRest (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit) : Prop where
  good : let F := keyFileDescription d.source d.numbers d.later
    let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
    (∀ L ∈ G.first, (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
        F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
    (∀ L ∈ G.shared, (L.withField 1 0 F.shared.blocksInOrder [] 0).goodAt (earlierOf F 1) .shared
        F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
    ∀ L ∈ G.second, ∀ base skip,
      (L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder base skip).goodAt (earlierOf F 2) .own
        F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃
  runs : let F := keyFileDescription d.source d.numbers d.later
    let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
    ∀ w₀ rc x, KeyRel files w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      ∃ r, runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r
  owed : let F := keyFileDescription d.source d.numbers d.later
    let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
    ∀ w₀ rc x, KeyRel files w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ r, ρ.due F = true →
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

/-- **The field `input`.** Where the index is in the statement's range it is in the prover's: the
two tests are one (E2E/KeyRangeOne.lean). The trace is `some ()` by the prover's definition. -/
theorem input_at (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : AtPublicFiles.KeyFile.KeyInst) (h : KeyRel files w₀ rc x) :
    ((partsOfDescription (files := files) d).prover d).inRange w₀ = true ∧
      (((partsOfDescription (files := files) d).prover d).trace w₀ x).isSome = true := by
  obtain ⟨s, x', -, hr⟩ := h
  exact ⟨(AtPublicFiles.AtFiles.HonestTerm.inRange_iff w₀).2 hr, rfl⟩

/-- Every owner has a row, at any book that is the written one. -/
theorem owns_at {Bk : ProverCoinCounts} {K₀ : KeyPub} (hB : Bk = keyBook K₀) (hK : fullPub = some K₀)
    {Z : PublicFiles} (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (c' : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    (offlineRowsAt (files := files) d Bk S c').owns = true := by
  subst hB
  exact offlineRows_owns _ hK (senderValue_atAll hs scope) (by show 0 < 2; omega) S _ c'

/-- **`Owed` at the key's rows, from what stays owed.** -/
theorem owed_of_rest (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hR : OwedRest d S c ((partsOfDescription (files := files) d).prover d)) :
    Owed (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      ((cmKey files).proverAt 0 ((partsOfDescription d).prover d))
      (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute (KeyRel files) := by
  have hP := isProvK_at (files := files) d S c (sized_sourced hs scope)
  have e : (cmKey files).proverAt 0 ((partsOfDescription d).prover d) =
      (partsOfDescription d).prover d := Committer.proverAt_self hP.key hP.stored
  rw [e]
  exact
    { plan := hs.named.plan
      book := by rw [offlineBook_eq hK]; exact AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK
      places := AtPublicFiles.KeyThread.placesOk_of_plan hs.named.plan
      seats := (seated_mute _).trans
        (offlineRows_seated _ _ scope hs.named (senderValue_atAll hs scope) S c)
      good := hR.good
      input := input_at d
      runs := hR.runs
      owed := hR.owed }

/-- **T3's three offline lines at the value**: conditional on `OwedRest` alone. -/
theorem offline_clauses (live : protocolDataWellFormed (asDescriptionFiles files) = true) (scope : InScope files = true)
    (hd : offlineDescription files = .ok d) (hs : KeySourced files d.source d.numbers d.later)
    (x₀ : XF) (hR : OwedRest d S c ((partsOfDescription (files := files) d).prover d)) :
    (∀ i r e, (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d)).ext
        (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
        (offlineSimulatorAt d (partsOfDescription (files := files) d)
          (offlineRowsAt (files := files) d offlineProverCoinCounts S c)) ∧
      PrivateStopsAtMost (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact offlineClauses hd (partsOfDescription d) scope live hs.named _
    (isProvK_at (files := files) d S c (sized_sourced hs scope)) x₀
    (owed_of_rest d S c hs scope hK hR)
    (owns_at d S (offlineBook_eq hK) hK hs scope c) (quiet_at d)

end Value

/-- **Where the public files' test says yes, in scope, T3's three offline lines stand at the named
value, but for the fields of `OwedRest`.** The value is `thePartsAt files`, which is
`partsOfDescription d`. -/
theorem offline_clauses_at_files (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) (x₀ : XF) :
    ∃ d : OfflineDescription, thePartsAt files = partsOfDescription d ∧
      ∀ (S : OfflineSimulators)
        (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness
          TableKey Unit Unit Unit),
        OwedRest d S c ((partsOfDescription (files := files) d).prover d) →
        ExactOutsideStops
          (AtPublicFiles.AtFiles.HonestTerm.offlineProver (partsOfDescription (files := files) d))
          (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
          (workAtFiles files).offline.cleared
          (offlineSimulatorAt d (partsOfDescription (files := files) d)
            (offlineRowsAt (files := files) d offlineProverCoinCounts S c)) := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named files live
  exact ⟨d, thePartsAt_ok hd, fun S c hR => (offline_clauses d S c live scope hd hs x₀ hR).2.1⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.isProvK_at
#print axioms AtPublicFiles.OfflineRows.quiet_at
#print axioms AtPublicFiles.OfflineRows.input_at
#print axioms AtPublicFiles.OfflineRows.owns_at
#print axioms AtPublicFiles.OfflineRows.owed_of_rest
#print axioms AtPublicFiles.OfflineRows.offline_clauses
#print axioms AtPublicFiles.OfflineRows.offline_clauses_at_files
