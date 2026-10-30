-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnOwedOfLots.lean: THE FIELD `ownTestOwed` OF `FourRowsOwed` (E2E/OfflineFourRowsLeft.lean), AT THE KEY FILE's RELATION AND THE
OFFLINE PROVER, FROM WHAT IS SPENT OF THE LOTS (`LotsSpent`, E2E/OfflineLotsSpent.lean: no field of it says yes) at the last chain's thread
and letter `lastThread`, `lastSaid` (E2E/OfflineLastTerms.lean).

  `own_atBlock_at_files`   in scope the last chain's sub-protocol number 2 is as `sayAtRun_second_guarded` asks, at the job at the
                         offline prover's own senders
  `own_half_at_files`      the prover of the muted rows has the job's pair behind the guard at the place
  `own_says_written`       `SayAtRun` at the own test, at the written book, where the family's third member is the thread's stand
  `ownOwed_of_spent`       the statement
  `ownOwed_of_lots`        the same from `TheLots`, by `lotsSpent_of_lots`

The road. At an input in the relation there is a seed at which it is tied, and there what is spent gives, at every coin k of
the book, that `ready` returns, that the plan serves, and a family of invariants whose third member is the thread's own
stand (`threads_at_spent`, E2E/OfflineLotsSpent.lean). At a called second part the walk's state lies behind such a stand
(`inside_called_second`, inside `sayAtRun_second_guarded`, E2E/OfflineSayOfThreads.lean). At every stand the rows taken in hold at the
job's words (`own_sayAtStand`, E2E/OwnSayAtValue.lean, with its premise on the key's sizes paid by `fit_at_tied`,
E2E/OfflineLastFit.lean). So `SayAtRun` holds at the run, and `owedAt_own_counted` with `trees_own_at_run` gives what is owed.

THE SENTENCE OF TRUTH IS SPENT INSIDE owed, AT EACH COIN k BY ITSELF: it reads k and, through the input, the committer's coins.
Nothing here is a law over coins, and none may be drawn from `own_says_written` as it stands.

Limits. CONDITIONAL on `LotsSpent`: no member is given here. In scope. What is laid at the place: hsim, hon, hpos. Nothing on
completeness, on soundness or on what is hidden.
-/
import E2E.OfflineOwnOwedAtFiles
import E2E.OfflineLastFit
import E2E.OfflineLotsSpent
import E2E.OfflineSharedTestsAtBlocks
import E2E.OwnSayAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (plainMany budBoth)
open ProofFile.Honest.K12.AtProof (placeW)
open ProofFile.Honest.K12.Sim2 (OnOwnTestEntry simOwnKey facts_KWFull rest_KW_pos)
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub ownTestPlace)
open AtPublicFiles.KeyLastChain (seat_own planPlays_KW place_own)
open AtPublicFiles.FirstH (LaterFill)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open H2K.Member (piKWFull codesKeyFull)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) ownOwedOfLotsPads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) ownOwedOfLotsRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) ownOwedOfLotsRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription}

/-- **In scope the last chain's sub-protocol number 2 is as the law asks.** -/
theorem own_atBlock_at_files (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) :
    ∃ b, (descOf d).second.blocksInOrder[2]? = some b ∧ b.place = ownTestPlace ∧
      ∃ s t rest, TestAtBlock (ownJobAtFiles (Z := Z) d).toRun.toTest b s t rest := by
  obtain ⟨b, hb, hseat⟩ := seat_own d.source d.numbers d.later (offlineSenders (files := Z) d).idx
    (offlineSenders (files := Z) d).w (offlineSenders (files := Z) d).send id
    (ProofFile.Honest.K12.Light.askOf (offlineSenders (files := Z) d).send
      (fun w => (offlineSenders (files := Z) d).weights w.w₀)
      fun w => randK14 ((offlineSenders (files := Z) d).rand w.rc))
  have hJ : (ownJobAtFiles (Z := Z) d).toRun.toTest.p = piKWFull := place_own hs scope
  have lists : b.oracles.length = b.rounds.length := by
    have h := ((planOk_all hs.named.plan).2.2 b (List.mem_of_getElem? hb)).2
    unfold Block.shaped at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  obtain ⟨s, t, rest, hst₀, hk⟩ := stages_own
  have hst : (ownJobAtFiles (Z := Z) d).toRun.toTest.p.nums.stages = s :: t :: rest := by
    rw [hJ]
    exact hst₀
  have P := planPlays_of_B (ownJobAtFiles (Z := Z) d).toRun.toTest s (t :: rest) hst 0 (by
    rw [hJ]
    exact planPlays_KW)
  refine ⟨b, hb, ?_, s, t, rest, testAtBlock_of_seat hseat hst hk P.plan P.sorts P.tables lists
    (by rw [hJ]; exact facts_KWFull.count) (by rw [hJ]; exact rest_KW_pos)⟩
  rw [hseat.place]
  exact own_job_place d hs scope

/-- **The prover of the muted rows has the job's pair behind the guard at the place.** -/
theorem own_half_at_files (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
      Unit) :
    (((offlineRowsAt (files := Z) d Bk S c).mute.prover ((partsOfDescription d).prover d)).second.find?
      fun g => g.place == ownTestPlace) =
      some (proverSideOfProximityTest (ownJobAtFiles (Z := Z) d).toRun.toTest).needsField := by
  rw [(provers_are_one (Z := Z) (d := d) Bk S c).2]
  have q := find_own (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d)
    (Xs := d.source) (N := d.numbers) (Pl := d.later) rfl
  rw [place_own hs scope] at q
  exact q

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)

/-- **`SayAtRun` at the own test, at the written book**, where the family's third member is the last thread's stand. -/
theorem own_says_written {S₁ : OwnLetter Z (keyBook K₀)}
    (scope : InScope Z = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {e : (protocolAtFiles Z).OutOfDomainSeed} {x : AtPublicFiles.AtFiles.KeyInst}
    (ht : TiedAt Z d (w₀, rc, e) x) {k : Coins (keyBook K₀)} {ρ : Draws} {r : RunC (descOf d)}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst TableKey Unit Unit Unit}
    (hR : ready (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k = .ok R)
    (hP : PlanServes ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc R)
    (T : ThreadsP (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k R)
    (h3 : T.I₃ = ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ (w₀, rc, e) x)
      (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ (w₀, rc, e) x))
    (hρ : ρ.due (descOf d) = true) (hsil : silentAt (descOf d) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x ρ = none)
    (hrun : runC (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k ρ = .ok r) :
    SayAtRun (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst Unit) (ownJobAtFiles (Z := Z) d).toRun.toTest
      (plainMany (ownJobAtFiles (Z := Z) d)) k 2 ownTestPlace r.called
      (midAtW (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k ρ) := by
  have hsay := own_sayAtStand ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ (w₀, rc, e) x hs scope hK₀
    (fun v hv => fit_at_tied d _ ℓ Nm Mg₀ _ rest Kp Vd (w₀, rc, e) x ht v hv)
  obtain ⟨b, hb, hbp, s, t, rs, B⟩ := own_atBlock_at_files (Z := Z) (d := d) hs scope
  have h := sayAtRun_second_guarded hrun hR hs.named.plan hρ hsil hP T
    (ownJobAtFiles (Z := Z) d).toRun.toTest (plainMany (ownJobAtFiles (Z := Z) d))
    (fun _ _ _ => rfl) 2 b hb s t rs B
    (by rw [hbp]; exact own_half_at_files hs scope (keyBook K₀) S c)
    (fun k' s' m' E' hI => by
      rw [h3] at hI
      obtain ⟨_, _, _, _, _, _, _, _, ho, _⟩ := hI.2.1 (Nat.le_refl 2)
      rw [ho]
      rfl)
    (fun st m₀ E₀ c' hI hl => hsay k st m₀ E₀ c' (by rw [h3] at hI; exact hI)
      (by rw [← hbp]; exact hl))
  rw [hbp] at h
  exact h

/-- **The field `ownTestOwed`, from what is spent of the lots.** -/
theorem ownOwed_of_spent {U₁ : FirstFamily Z d (keyBook K₀)} {S₁ : OwnLetter Z (keyBook K₀)}
    (scope : InScope Z = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d U₁
      (fun w x => lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) S₁
      (fun w x => lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit)
    (hsim : S.ownTest = [firstSim (simOwnKey d.source d.numbers d.later),
      restSim (simOwnKey d.source d.numbers d.later)])
    (hon : (c.second ownTestPlace).atPart = OnOwnTestEntry Face.own (ownJobAt (files := Z) d)
      (simOwnKey d.source d.numbers d.later) codesKeyFull 2 piKWFull.nums.first)
    (hpos : (c.second ownTestPlace).positions = budBoth (simOwnKey d.source d.numbers d.later)) :
    OwedLastAt (files := Z) d S c
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK)
      ((partsOfDescription (files := Z) d).prover d) ownTestPlace := by
  refine owedLastAt_own_rel d S c ((partsOfDescription (files := Z) d).prover d) _ _ _
    (fun a => ⟨a.2, rfl⟩) hs scope hK₀ hsim hon hpos ?_
  have key : ∀ (Bk : ProverCoinCounts) (_ : Bk = keyBook K₀)
      (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
        Unit),
      ∀ w₀ rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x →
      ∀ (k : Coins Bk) ρ r, ρ.due (descOf d) = true →
        silentAt (descOf d) ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x ρ = none →
        runC (descOf d) Bk ((offlineRowsAt (files := Z) d Bk S c).mute.prover
          ((partsOfDescription d).prover d)) w₀ rc x k ρ = .ok r →
        SayAtRun (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst Unit) (ownJobAt (files := Z) d)
          (plainMany (ownManyAt (files := Z) d)) k 2 placeW r.called
          (midAtW (descOf d) Bk ((offlineRowsAt (files := Z) d Bk S c).mute.prover
            ((partsOfDescription d).prover d)) w₀ rc x k ρ) := by
    intro Bk hB
    subst hB
    intro c w₀ rc x hrel k ρ r hρ hsil hrun
    obtain ⟨e, ht, hk⟩ := threads_at_spent ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ scope hs L S c w₀ rc x hrel
    obtain ⟨R, hR, hP, T, -, -, h3⟩ := hk k
    exact own_says_written ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ Q scope hK₀ hs S c ht hR hP T h3 hρ hsil hrun
  exact key offlineProverCoinCounts (offlineBook_eq hK₀) c

/-- **The same from the lots.** -/
theorem ownOwed_of_lots {U₁ : FirstFamily Z d (keyBook K₀)} {S₁ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (L : TheLots (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d U₁
      (fun w x => lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) S₁
      (fun w x => lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit)
    (hsim : S.ownTest = [firstSim (simOwnKey d.source d.numbers d.later),
      restSim (simOwnKey d.source d.numbers d.later)])
    (hon : (c.second ownTestPlace).atPart = OnOwnTestEntry Face.own (ownJobAt (files := Z) d)
      (simOwnKey d.source d.numbers d.later) codesKeyFull 2 piKWFull.nums.first)
    (hpos : (c.second ownTestPlace).positions = budBoth (simOwnKey d.source d.numbers d.later)) :
    OwedLastAt (files := Z) d S c
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK)
      ((partsOfDescription (files := Z) d).prover d) ownTestPlace :=
  ownOwed_of_spent ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ Q scope hK₀ hs
    (lotsSpent_of_lots ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ hd scope live hK₀ hN hKp hE hEnd hC L) S c hsim hon
    hpos

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.own_atBlock_at_files
#print axioms AtPublicFiles.OfflineRows.own_half_at_files
#print axioms AtPublicFiles.OfflineRows.own_says_written
#print axioms AtPublicFiles.OfflineRows.ownOwed_of_spent
#print axioms AtPublicFiles.OfflineRows.ownOwed_of_lots
