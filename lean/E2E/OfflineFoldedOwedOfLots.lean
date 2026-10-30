-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFoldedOwedOfLots.lean: THE FIELD owed OF OwedRest (E2E/OfflineClauses.lean) AT THE ROW OF THE PROXIMITY TEST ON THE FOLDED ROW's
GROUP (the shared chain's sub-protocol number 9), FROM WHAT IS SPENT OF THE OFFLINE PROVER's DEBTS ON ACCEPTANCE ALONE (`LotsSpent`,
E2E/OfflineLotsSpent.lean: no field of it says that anything accepts), at every value of the join's letters.

  `folded_atBlock_at_files`   in scope the sub-protocol at the place is as `TestAtBlock` asks, at the job at the offline
                              prover's own senders
  `folded_half_at_files`      the prover of the muted rows has that job's half at the place
  `folded_says_written`       at the written book: at every input in the key file's relation, every coin, every run that
                              has returned: `SayAtRun` (E2E/OfflineSayAtRun.lean) at the test
  `foldedOwed_of_lots`        `OwedSharedAt … foldedTestPlace` (E2E/OfflineRowsByPlace.lean), at `offlineProverCoinCounts`

The chain. `threads_at_spent` (E2E/OfflineLotsSpent.lean): the relation gives a seed at which the input is tied, and at that seed
and every coin a member of `ThreadsP` whose second family of invariants is the shared thread's own sentence with its letter · `say_at_folded` (E2E/OfflineSayAtFolded.lean): at every stand of
that invariant at the border 9 the rows that the test takes in say true · `sayAtRun_shared`, through `inside_called_shared`
(E2E/OfflineSayOfThreads.lean): the called second part of a run that has returned stands behind such a stand ·
`owed_folded_of_say` (E2E/OfflineFoldedLeft.lean).

WHERE THE SENTENCE ON THE COINS IS SPENT. `say_at_folded` reads the input and the coins. It is spent INSIDE the field owed: at one
input, one coin k and one run that has returned at k; no law over coins stands behind it here.

NO PREMISE OF TRUTH IS LEFT AT THIS ROW. Asked of the simulators and the letters: `FoldedLetters` (E2E/OfflineFoldedAtRows.lean).

Limits. CONDITIONAL on `LotsSpent`: no thread is shown here to meet any of its fields. Nothing on any property.
-/
import E2E.OfflineLotsSpent
import E2E.OfflineSharedTestsAtBlocks
import E2E.OfflineSayAtFolded
import E2E.OfflineFoldedLeft
import E2E.OfflineRowsByPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (plainMany)
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens SendPub)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeySharedThread (parKey plan_key)
open AtPublicFiles.KeyValueHolds (place_p12At)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced)
open AtPublicFiles.OfflineRows.Folded (FoldedLetters owed_folded_of_say)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) foldedOwedOfLotsPads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) foldedOwedOfLotsRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) foldedOwedOfLotsRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles}

/-- **In scope the sub-protocol at the place is as the law asks**, at the job at the offline prover's own senders. -/
theorem folded_atBlock_at_files {d : OfflineDescription}
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (b : Block (descOf d).S₂ (descOf d).Cl) (hb : b ∈ (descOf d).shared.blocksInOrder)
    (hp : b.place = foldedTestPlace) :
    ∃ s t rest, TestAtBlock (foldedJobAtFiles (Z := Z) d).toRun.toTest b s t rest := by
  have lists : b.oracles.length = b.rounds.length := by
    have h := ((planOk_all hs.named.plan).2.1 b hb).2
    unfold Block.shaped at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  obtain ⟨src, num, later⟩ := d
  obtain rfl : later = PF := later_sourced hs scope
  obtain rfl := sharedBlock_folded hs scope b hb hp
  have e : parKey src PF = QK := par_sourced hs scope
  exact foldedTest_atBlock (offlineSenders (files := Z) ⟨src, num, PF⟩).send
    (by
      show (⟨parKey src PF, 0⟩ : SendPub) = _
      rw [e]) _ _ _ _ lists

variable {d : OfflineDescription}

/-- **The prover of the muted rows has the job's half at the place.** -/
theorem folded_half_at_files (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
      Unit) :
    (((offlineRowsAt (files := Z) d Bk S c).mute.prover ((partsOfDescription d).prover d)).shared.find?
      fun g => g.place == foldedTestPlace) =
      some (proverSideOfProximityTest (foldedJobAtFiles (Z := Z) d).toRun.toTest) := by
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  rw [(provers_are_one (Z := Z) (d := d) Bk S c).2]
  exact (shared_finds (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) hQ.facts.two (place_p12At _ _)
    (place_p12At _ _)).1

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)

/-- **`SayAtRun` at the test on the folded row's group, at the written book**, at a member of `ThreadsP` whose second family is the shared thread's own. -/
theorem folded_says_written (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {e : (protocolAtFiles Z).OutOfDomainSeed} {x : AtPublicFiles.AtFiles.KeyInst}
    (ht : TiedAt Z d (w₀, rc, e) x) {k : Coins (keyBook K₀)} {ρ : Draws} {r : RunC (descOf d)}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst TableKey Unit Unit Unit}
    (hR : ready (descOf d) (keyBook K₀)
      ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
      w₀ rc x k = .ok R)
    (T : ThreadsP (descOf d) (keyBook K₀)
      ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
      w₀ rc x k R)
    (h2 : T.I₂ = ThrS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x)
      (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x))
    (hρ : ρ.due (descOf d) = true)
    (hsil : silentAt (descOf d)
      ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
      w₀ rc x ρ = none)
    (hrun : runC (descOf d) (keyBook K₀)
      ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
      w₀ rc x k ρ = .ok r) :
    SayAtRun Empty (foldedJobAtFiles (Z := Z) d).toRun.toTest (plainMany (foldedJobAtFiles (Z := Z) d)) k 1
      foldedTestPlace r.called
      (midSharedAtW (descOf d) (keyBook K₀)
        ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
        w₀ rc x k ρ) := by
  have hsay := say_at_folded ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ hd scope live hK₀ (w₀, rc, e) x ht
  obtain ⟨-, hb9, -, -⟩ := borders_are_the_tests hs scope
  obtain ⟨b, hb, hbp⟩ := Option.map_eq_some_iff.1 hb9
  obtain ⟨s, t, rs, Q⟩ := folded_atBlock_at_files hs scope b (List.mem_of_getElem? hb) hbp
  have h := sayAtRun_shared hrun hR hs.named.plan hρ hsil T
    (foldedJobAtFiles (Z := Z) d).toRun.toTest (plainMany (foldedJobAtFiles (Z := Z) d))
    (fun _ _ _ => rfl) 9 b hb s t rs Q
    (by rw [hbp]; exact folded_half_at_files hs scope (keyBook K₀) S c)
    (fun st m₀ E₀ c' hI hl => hsay k st m₀ E₀ c' (by rw [h2] at hI; exact hI)
      (by rw [← hbp]; exact hl))
  rw [hbp] at h
  exact h

/-- **The field `testOnFoldedRowOwed`, from what is spent of the lots.** -/
theorem foldedOwed_of_lots {U₁ : FirstFamily Z d (keyBook K₀)} {U₃ : LastFamily Z d (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d U₁ U₃ S₁ S₃) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit)
    (hc : FoldedLetters (Xs := d.source) (N := d.numbers) (Pl := d.later)
      (senderValue (files := Z) d) S c) :
    OwedSharedAt (files := Z) d S c
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK)
      ((partsOfDescription (files := Z) d).prover d) foldedTestPlace := by
  have key : ∀ (Bk : ProverCoinCounts) (_ : Bk = keyBook K₀)
      (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
        Unit),
      FoldedLetters (Xs := d.source) (N := d.numbers) (Pl := d.later) (senderValue (files := Z) d) S
        c →
      ∀ w₀ rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x →
      ∀ (k : Coins Bk) ρ r, ρ.due (descOf d) = true →
        silentAt (descOf d) ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x ρ = none →
        runC (descOf d) Bk ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x k ρ = .ok r →
        ∀ Lr ∈ (offlineRowsAt (files := Z) d Bk S c).mute.shared, Lr.place = foldedTestPlace →
          Lr.owedAt (descOf d).shared.blocksInOrder k 1
            (fun a => orRefused (midSharedAtW (descOf d) Bk
              ((offlineRowsAt (files := Z) d Bk S c).mute.prover ((partsOfDescription d).prover d)) w₀
              rc x k ρ a)) r.run
            (storedShown (((partsOfDescription d).prover d).storedWords w₀ rc) r.run.storedAsked)
            r.called := by
    intro Bk hB
    subst hB
    intro c hc w₀ rc x hrel k ρ r hρ hsil hrun
    obtain ⟨e, ht, hk⟩ := threads_at_spent ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ scope hs L S c w₀ rc x hrel
    obtain ⟨R, hR, -, T, -, h2, -⟩ := hk k
    obtain ⟨layO, hQ⟩ := plan_key hs scope
    exact owed_folded_of_say scope hs hK₀ rfl (senderValue (files := Z) d) rfl hQ.facts.two rfl
      (place_p12At _ _) S c hc ((partsOfDescription d).prover d) rfl T hρ hsil hR hrun
      (folded_says_written ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ hd scope live hK₀ hs S c ht
        hR T h2 hρ hsil hrun)
  exact key offlineProverCoinCounts (offlineBook_eq hK₀) c hc

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.folded_atBlock_at_files
#print axioms AtPublicFiles.OfflineRows.folded_half_at_files
#print axioms AtPublicFiles.OfflineRows.folded_says_written
#print axioms AtPublicFiles.OfflineRows.foldedOwed_of_lots
