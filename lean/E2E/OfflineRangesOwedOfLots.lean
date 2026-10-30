-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRangesOwedOfLots.lean: THE FIELD owed OF OwedRest (E2E/OfflineClauses.lean) AT THE ROW OF THE PROXIMITY TEST ON THE
RANGES, FROM WHAT IS SPENT OF THE OFFLINE PROVER's DEBTS ON ACCEPTANCE ALONE (`LotsSpent`, E2E/OfflineLotsSpent.lean: no field of it
says yes; `TheLots` gives it), taken at the first chain's own thread (`firstFamilyAt d Q`, E2E/OfflineFirstFamilyAtTerm.lean; Q a letter).

  `owed_ranges_written`   at the written book `keyBook K₀`: at every input in the key file's relation, every coin, every
                          run that has returned: `owedAt` at the muted row at `rngPlace`
  `owed_ranges_of_lots`   the same as `OwedFirstAt … rngPlace` (E2E/OfflineRowsByPlace.lean), at `offlineProverCoinCounts`

The chain. `threads_at_spent` (E2E/OfflineLotsSpent.lean): a member of `ThreadsP` whose first family of invariants
is the thread's own sentence with its letter · `thr_at_term`: that invariant at the border 15 gives the thread's sentence ·
`onAtRun_ranges_one` (E2E/OfflineRangesOwes.lean): there the rows that the test takes in say true, by the thread's own lines,
and the condition at the second part's entry holds at the run · the row and the prover's two sides at their places
(`ranges_row_is`, `ranges_halves_found`, E2E/OfflineRangesOwedAtRows.lean) · the budget (`budOwed₁_at_KR`, Johnson/M1/KeyBudR.lean) ·
`owedAt_first_of_onAtRun` (E2E/OfflineOwedRowAtRun.lean).

NO PREMISE OF TRUTH IS LEFT AT THIS ROW. Asked of the simulators and the letters: at `rngPlace` they are the row's own (hS, hcOn,
hcBud).

ON THE COINS. The condition at the second part's entry (On) reads the input and the carried coins. Here it is OWED: it is shown
at every input in the relation, AT EVERY COIN k of the book and every due list of challenges, at the run's own stand:
nowhere is it a hypothesis on a run under which coins are then sampled anew, and no law here conditions the coins on it. The
lemma that gives the stand at every coin is named beside the call: `threads_at_spent` (∃ seed, ∀ k, ∃ R, a member of
`ThreadsP` at k): the explicit input is the relation's own written key at that seed, one seed for all coins; `owes_at_ranges`
(within `onAtRun_ranges_one`) holds at all coins.

Limits. CONDITIONAL on `LotsSpent`: no thread is shown here to meet any of its fields. Nothing on any property.
-/
import E2E.OfflineLotsSpent
import E2E.OfflineFirstFamilyAtTerm
import E2E.OfflineRangesOwes
import E2E.OfflineRangesOwedAtRows
import E2E.OfflineRowsByPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.KeyThread (rangesTestJob place_sourced)
open AtPublicFiles.FirstH (LaterFill)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K12.Light (budBoth PlaceFacts)
open H2K.Member (piKRFull codesKeyFull)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) rangesOwedOfLotsPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) rangesOwedOfLotsValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) rangesOwedOfLotsDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription}

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)

/-- **`owedAt` at the row of the test on the ranges, from the lots, at the written book.** -/
theorem owed_ranges_written (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
    {U₃ : LastFamily Z d (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (scope : InScope Z = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (firstFamilyAt d Q) U₃ S₁ S₃)
    (S : OfflineSimulators)
    (hS : S.rangesTest = [firstSim (simRanges d.source d.numbers d.later),
      restSim (simRanges d.source d.numbers d.later)])
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit)
    (hcOn : (c.first rngPlace).atPart = OnEntry Face.own
      (rangesTestJob (X' := Unit) d.source d.numbers d.later (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0)
      (simRanges d.source d.numbers d.later) codesKeyFull 0 piKRFull.nums.first)
    (hcBud : (c.first rngPlace).positions = budBoth (simRanges d.source d.numbers d.later)) :
    ∀ w₀ rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x →
    ∀ (k : Coins (keyBook K₀)) ρ r, ρ.due (descOf d) = true →
      silentAt (descOf d) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x ρ = none →
      runC (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k ρ = .ok r →
      ∀ Lr ∈ (offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.first, Lr.place = rngPlace →
        Lr.owedAt (descOf d).first.blocksInOrder k 0
          (fun a => orRefused (midAtW (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k ρ a)) r.run
          (storedShown (((partsOfDescription d).prover d).storedWords w₀ rc) r.run.storedAsked)
          r.called := by
  intro w₀ rc x hrel k ρ r hρ hsil hrun
  -- the stand AT EVERY COIN: one seed e, then ∀ k: `threads_at_spent`
  obtain ⟨e, -, hk⟩ := threads_at_spent ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ scope hs L S c w₀ rc x hrel
  have hkk := hk k
  rw [prover_mute] at hsil hrun hkk ⊢
  obtain ⟨R, hR, -, T, h1, -, -⟩ := hkk
  have hI := fun s m E => thr_at_term d Q T e h1 15 k s m E
  intro Lr hLr hp
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hLr
  refine (owedAt_mute L' _ _ _ _ _ _ _).2 ?_
  have hp' : L'.place = rngPlace := hp
  have hA := (senderValue_atAll (files := Z) hs scope).first
  obtain ⟨hrow, hOn, hbud⟩ := ranges_row_is (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0
    (senderValue (files := Z) d) hA rfl S hS c L' hL' hp'
  obtain ⟨f1, f2⟩ := ranges_halves_found (senderValue (files := Z) d) hA
  have hJ : (rangesTestJob (X' := Unit) d.source d.numbers d.later (matrixEntryOf (Rc := (protocolAtFiles Z).EncodingRandomness) matrixReader)
      (multiplicitiesGroups d.source) 0).p = piKRFull := place_sourced hs scope
  have hPR : (rangesTestJob (X' := Unit) d.source d.numbers d.later (matrixEntryOf (Rc := (protocolAtFiles Z).EncodingRandomness) matrixReader)
      (multiplicitiesGroups d.source) 0).p.place = rngPlace := by
    rw [hJ]
    exact place_KR
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_ranges scope hs.named
    (rangesTestJob (X' := Unit) d.source d.numbers d.later (matrixEntryOf (Rc := (protocolAtFiles Z).EncodingRandomness) matrixReader)
      (multiplicitiesGroups d.source) 0) rfl
  have F : PlaceFacts (rangesTestJob (X' := Unit) d.source d.numbers d.later
      (matrixEntryOf (Rc := (protocolAtFiles Z).EncodingRandomness) matrixReader) (multiplicitiesGroups d.source) 0).p dsKR := by
    rw [hJ]
    exact facts_KRFull
  refine owedAt_first_of_onAtRun hs.named.plan (AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK₀) hρ
    hsil hR hrun T hL' ?_ ?_
  · intro σ hσ u hu pre t n hcut hn
    exact OnBytes.M1.KeyBud.budOwed₁_at_KR scope hs.named L'
      (rangesTestJob (X' := Unit) d.source d.numbers d.later (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0) F
      (by rw [hJ]) hPR hf hbp hr hor rfl (simRanges d.source d.numbers d.later) hJ.symm rfl
      (hp'.trans hPR.symm) hrow (fun n ds asks h => by rw [hbud, hcBud]; exact h) σ hσ u hu pre t n
      hcut hn ρ hρ
  · refine onAtRun_ranges_one (K := AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)
      (f := matrixReader) (Q := Q) scope hs hK₀ (firstPublic_at_term d hs scope) T hρ hR hrun 1 L' hp'
      hrow (hOn.trans hcOn) ?_ ?_ ?_ hI
    · rw [offlineRows_prover_at]
      rfl
    · rw [offlineRows_prover_at]
      exact f1
    · rw [offlineRows_prover_at]
      exact f2.trans (congrArg (fun j => some (K1.proverSideOfSending j)) (firstPublic_at_term d hs scope).msg)

/-- **The field `rangesTestOwed`, from the lots.** -/
theorem owed_ranges_of_lots (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
    {U₃ : LastFamily Z d (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (scope : InScope Z = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (firstFamilyAt d Q) U₃ S₁ S₃)
    (S : OfflineSimulators)
    (hS : S.rangesTest = [firstSim (simRanges d.source d.numbers d.later),
      restSim (simRanges d.source d.numbers d.later)])
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit)
    (hcOn : (c.first rngPlace).atPart = OnEntry Face.own
      (rangesTestJob (X' := Unit) d.source d.numbers d.later (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0)
      (simRanges d.source d.numbers d.later) codesKeyFull 0 piKRFull.nums.first)
    (hcBud : (c.first rngPlace).positions = budBoth (simRanges d.source d.numbers d.later)) :
    OwedFirstAt (files := Z) d S c
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK)
      ((partsOfDescription (files := Z) d).prover d) rngPlace := by
  have key : ∀ (Bk : ProverCoinCounts) (_ : Bk = keyBook K₀)
      (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
        Unit),
      (c.first rngPlace).atPart = OnEntry Face.own
        (rangesTestJob (X' := Unit) d.source d.numbers d.later (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0)
        (simRanges d.source d.numbers d.later) codesKeyFull 0 piKRFull.nums.first →
      (c.first rngPlace).positions = budBoth (simRanges d.source d.numbers d.later) →
      ∀ w₀ rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x →
      ∀ (k : Coins Bk) ρ r, ρ.due (descOf d) = true →
        silentAt (descOf d) ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x ρ = none →
        runC (descOf d) Bk ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x k ρ = .ok r →
        ∀ Lr ∈ (offlineRowsAt (files := Z) d Bk S c).mute.first, Lr.place = rngPlace →
          Lr.owedAt (descOf d).first.blocksInOrder k 0
            (fun a => orRefused (midAtW (descOf d) Bk ((offlineRowsAt (files := Z) d Bk S c).mute.prover
              ((partsOfDescription d).prover d)) w₀ rc x k ρ a)) r.run
            (storedShown (((partsOfDescription d).prover d).storedWords w₀ rc) r.run.storedAsked)
            r.called := by
    intro Bk hB
    subst hB
    intro c h1 h2
    exact owed_ranges_written ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ Q scope hK₀ hs L S hS c h1 h2
  exact key offlineProverCoinCounts (offlineBook_eq hK₀) c hcOn hcBud

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.owed_ranges_written
#print axioms AtPublicFiles.OfflineRows.owed_ranges_of_lots
