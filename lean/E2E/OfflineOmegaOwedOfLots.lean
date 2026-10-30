-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaOwedOfLots.lean: THE FIELD owed OF OwedRest (E2E/OfflineClauses.lean) AT THE ROW OF THE PROXIMITY TEST ON OMEGA's GROUP (the shared
chain's sub-protocol number 10), FROM WHAT IS SPENT OF THE OFFLINE PROVER's DEBTS ON ACCEPTANCE ALONE (`LotsSpent`,
E2E/OfflineLotsSpent.lean: no field of it says that anything accepts), at the
table's letter `ttLaid` (E2E/OfflineSayAtOmega.lean) and the letter `keepsKey`, at every other value of the join's letters.

  `omega_atBlock_at_files`   in scope the sub-protocol at the place is as `TestAtBlock` asks, at the job at the offline prover's
                             own senders
  `omega_half_at_files`      the prover of the muted rows has that job's half, behind the guard, at the place
  `open_at_omega`            at every stand of the shared thread's own sentence at the border 10 columns are handed: by
                             `fields_made_at_key` (Johnson/Desc/ProofFile/Honest/K12/AtKey/UOStand.lean) and `field_of_walked` (…/AtKey/UWalked.lean), called as
                             `say_at_stand_at_laid_ten` (…/AtKey/OSayLaid.lean) calls them; the stand is read as in
                             `five_at_ten_key` (…/AtKey/OStep.lean). NOT IN FRONT OF A LAW OVER COINS, as the laws that it calls
  `omega_says_written`       at the written book: at a tied input, every coin, every run that has returned: `SayAtRun`
                             (E2E/OfflineSayAtRun.lean) at the test
  `omegaOwed_of_lots`        `OwedSharedAt … omegaTestPlace` (E2E/OfflineRowsByPlace.lean), at `offlineProverCoinCounts`

The chain. `threads_at_spent` (E2E/OfflineLotsSpent.lean): the relation gives a seed at which the input is tied, and at that seed
and every coin a member of `ThreadsP` whose second family of invariants is the shared thread's own sentence with its letter · `say_at_omega` (E2E/OfflineSayAtOmega.lean): at every stand of
that invariant at the border 10 the rows that the test takes in say true · `sayAtRun_shared_guarded`, through
`inside_called_shared` (E2E/OfflineSayOfThreads.lean): the called second part of a run that has returned stands behind such a
stand · `omega_owed_of_say` (E2E/OfflineOmegaDoor.lean).

WHERE THE SENTENCES ON THE COINS ARE SPENT. `say_at_omega` and `open_at_omega` read the input and the coins. They are spent INSIDE the
field owed: at one input, one coin k and one run that has returned at k; no law over coins stands behind them here.

NO PREMISE OF TRUTH IS LEFT AT THIS ROW. Asked of the simulators and the letters: `OmegaLetters`
(E2E/OfflineOmegaOwedAtFiles.lean).

Limits. CONDITIONAL on `LotsSpent`: no thread is shown here to meet any of its fields. Nothing on any property.
-/
import E2E.OfflineLotsSpent
import E2E.OfflineSharedTestsAtBlocks
import E2E.OfflineSayAtOmega
import E2E.OfflineOmegaOwedAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (plainMany budBoth OnOmegaKey sentOf stateAtOmega)
open ProofFile.Honest.K12.AtKey (keepsKey field_of_walked fields_made_at_key)
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K14 (WitLens SendPub)
open H2K.Member (piKOFull)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeySharedThread (parKey plan_key)
open AtPublicFiles.KeyValueHolds (place_p12At)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega jobKO bsOf wtOf rdOf)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.StandAtNine (K1)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) omegaOwedOfLotsPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) omegaOwedOfLotsValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) omegaOwedOfLotsDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles}

/-- **In scope the sub-protocol at the place is as the law asks**, at the job at the offline prover's own senders. -/
theorem omega_atBlock_at_files {d : OfflineDescription}
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (b : Block (descOf d).S₂ (descOf d).Cl) (hb : b ∈ (descOf d).shared.blocksInOrder)
    (hp : b.place = omegaTestPlace) :
    ∃ s t rest, TestAtBlock (omegaJobAtFiles (Z := Z) d).toRun.toTest b s t rest := by
  have lists : b.oracles.length = b.rounds.length := by
    have h := ((planOk_all hs.named.plan).2.1 b hb).2
    unfold Block.shaped at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  obtain ⟨src, num, later⟩ := d
  obtain rfl : later = PF := later_sourced hs scope
  obtain rfl := sharedBlock_omega hs scope b hb hp
  have e : parKey src PF = QK := par_sourced hs scope
  exact omegaTest_atBlock (offlineSenders (files := Z) ⟨src, num, PF⟩).send
    (by
      show (⟨parKey src PF, 0⟩ : SendPub) = _
      rw [e]) _ _ _ _ lists

variable {d : OfflineDescription}

/-- **The prover of the muted rows has the job's half, behind the guard, at the place.** -/
theorem omega_half_at_files (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
      Unit) :
    (((offlineRowsAt (files := Z) d Bk S c).mute.prover ((partsOfDescription d).prover d)).shared.find?
      fun g => g.place == omegaTestPlace) =
      some (proverSideOfProximityTest (omegaJobAtFiles (Z := Z) d).toRun.toTest).needsField := by
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  rw [(provers_are_one (Z := Z) (d := d) Bk S c).2]
  exact (shared_finds (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) hQ.facts.two (place_p12At _ _)
    (place_p12At _ _)).2

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF))

/-- **At every stand of the shared thread's own sentence at the border 10 columns are handed.** -/
theorem open_at_omega (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hN : Function.Injective Nm.tenant) :
    ∀ w x, TiedAt Z d w x → ∀ k s m E,
      ThrS (sharedThread ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d w x)
        (sharedSaid ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d w x) 10 k s m E →
      m.opened.isSome = true := by
  intro w x ht
  obtain ⟨sd, hx⟩ := key_at_tied hd scope live Z₀ w x ht
  have hs := sourced_of_ok live hd
  clear hd ht
  obtain ⟨src, num, later⟩ := d
  obtain rfl : later = PF := later_sourced hs scope
  have F := fields_made_at_key src num K₀ (sendersFront Z ⟨src, num, PF⟩) ℓ Nm Mg₀ tk rest Vd matrixReader
    (tableCoins Z) Z₀ w.1 w.2.1 x B () hs scope sd hx
  have hf := field_of_walked K₀ hK₀ src num
    (K1 src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀) ℓ Nm Mg₀ tk rest Vd w.1 w.2.1 x B ()
    (fun _ m => m = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ src.chains) src PF
                { withTestsOnUAndOmega (K1 src (sendersFront Z ⟨src, num, PF⟩) matrixReader (tableCoins Z) Z₀) pU pO with
                  rng := (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) ⟨src, num, PF⟩).rng
                  own := (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) ⟨src, num, PF⟩).own }
                matrixReader (tableCoins Z)) (some []) (inK w.1 w.2.1 x))
    hs scope F rfl rfl hN (fun _ _ h => h ▸ saidField_start _ rfl)
  intro k s m E u
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, -, hc, -⟩, -, -⟩ := u.1
  rw [hf k s m E u cols hc]
  rfl

/-- **`SayAtRun` at the test on Omega's group, at the written book**, at a member of `ThreadsP` whose second family is the shared thread's own. -/
theorem omega_says_written (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (S : OfflineSimulators)
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
    (h2 : T.I₂ = ThrS (sharedThread ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d (w₀, rc, e) x)
      (sharedSaid ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d (w₀, rc, e) x))
    (hρ : ρ.due (descOf d) = true)
    (hsil : silentAt (descOf d)
      ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
      w₀ rc x ρ = none)
    (hrun : runC (descOf d) (keyBook K₀)
      ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
      w₀ rc x k ρ = .ok r) :
    SayAtRun Empty (omegaJobAtFiles (Z := Z) d).toRun.toTest (plainMany (omegaJobAtFiles (Z := Z) d)) k 1
      omegaTestPlace r.called
      (midSharedAtW (descOf d) (keyBook K₀)
        ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
        w₀ rc x k ρ) := by
  have hsay := say_at_omega ℓ Nm Mg₀ tk rest Vd Z₀ B hd scope live hK₀ hN (w₀, rc, e) x ht
  have hopen := open_at_omega ℓ Nm Mg₀ tk rest Vd Z₀ B hd scope live hK₀ hN (w₀, rc, e) x ht
  obtain ⟨-, -, hb10, -⟩ := borders_are_the_tests hs scope
  obtain ⟨b, hb, hbp⟩ := Option.map_eq_some_iff.1 hb10
  obtain ⟨s, t, rs, Q⟩ := omega_atBlock_at_files hs scope b (List.mem_of_getElem? hb) hbp
  have h := sayAtRun_shared_guarded hrun hR hs.named.plan hρ hsil T
    (omegaJobAtFiles (Z := Z) d).toRun.toTest (plainMany (omegaJobAtFiles (Z := Z) d))
    (fun _ _ _ => rfl) 10 b hb s t rs Q
    (by rw [hbp]; exact omega_half_at_files hs scope (keyBook K₀) S c)
    (fun k' s' m' E' hI => hopen k' s' m' E' (by rw [h2] at hI; exact hI))
    (fun st m₀ E₀ c' hI hl => hsay k st m₀ E₀ c' (by rw [h2] at hI; exact hI)
      (by rw [← hbp]; exact hl))
  rw [hbp] at h
  exact h

/-- **The field `testOnOmegaOwed`, from what is spent of the lots.** -/
theorem omegaOwed_of_lots {U₁ : FirstFamily Z d (keyBook K₀)} {U₃ : LastFamily Z d (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d U₁ U₃ S₁ S₃)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit) (Js : SimJob TableKey) (hc : OmegaLetters (files := Z) d S c Js) :
    OwedSharedAt (files := Z) d S c
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK)
      ((partsOfDescription (files := Z) d).prover d) omegaTestPlace := by
  have key : ∀ (Bk : ProverCoinCounts) (_ : Bk = keyBook K₀)
      (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
        Unit),
      ∀ w₀ rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x →
      ∀ (k : Coins Bk) ρ r, ρ.due (descOf d) = true →
        silentAt (descOf d) ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x ρ = none →
        runC (descOf d) Bk ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x k ρ = .ok r →
        SayAtRun Empty (omegaJobAtSenders (files := Z) d).toRun.toTest
          (plainMany (omegaJobAtSenders (files := Z) d)) k 1 omegaTestPlace r.called
          (midSharedAtW (descOf d) Bk ((offlineRowsAt (files := Z) d Bk S c).mute.prover
            ((partsOfDescription d).prover d)) w₀ rc x k ρ) := by
    intro Bk hB
    subst hB
    intro c w₀ rc x hrel k ρ r hρ hsil hrun
    obtain ⟨e, ht, hk⟩ := threads_at_spent ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ scope hs L S c
      w₀ rc x hrel
    obtain ⟨R, hR, -, T, -, h2, -⟩ := hk k
    exact omega_says_written ℓ Nm Mg₀ tk rest Vd Z₀ B hd scope live
      hK₀ hs hN S c ht hR T h2 hρ hsil hrun
  exact omega_owed_at_files d S c _ _ hs scope live (fun _ => rfl) Js hc
    (key offlineProverCoinCounts (offlineBook_eq hK₀) c)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.omega_atBlock_at_files
#print axioms AtPublicFiles.OfflineRows.omega_half_at_files
#print axioms AtPublicFiles.OfflineRows.open_at_omega
#print axioms AtPublicFiles.OfflineRows.omega_says_written
#print axioms AtPublicFiles.OfflineRows.omegaOwed_of_lots
