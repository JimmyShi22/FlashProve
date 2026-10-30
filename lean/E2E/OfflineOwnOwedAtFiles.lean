-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnOwedAtFiles.lean: THE FIELD `ownTestOwed` OF `FourRowsOwed` (E2E/OfflineFourRowsLeft.lean), in its own type:
`OwedLastAt d S c Rel H ownTestPlace` (E2E/OfflineRowsByPlace.lean): what is owed at every returned run at the offline file's
row of the own proximity test, at the offline prover's own senders and the written book: FROM ONE NAMED PREMISE ON THE
RUNS, `OwnRunsSay`: THE ONE CLAUSE OF TRUTH.

  `ownManyAt`, `ownJobAt`   the job that the offline prover's senders lay at the own test
  `OwnRunsSay`            THE NAMED PREMISE: under Rel, at every returned run outside the stops: `SayAtRun`
                        (E2E/OfflineSayAtRun.lean): at the called second part the rows taken in hold at the job's words
  `owedLastAt_own`        the statement, at a relation under which every instance's key has the written sizes
  `owedLastAt_own_rel`    the same at every relation `relAt` (Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean) whose writing map
                        writes `keyInstanceOfOutOfDomainSample` of the sample: the key file's relation is one

What is laid at the place: hsim: the two simulators; hon: the row's condition is `OnOwnTestEntry` at the job; hpos: its
`bud` is `budBoth`.
By `owedAt_own_counted` (E2E/OfflineOwnOwedCounted.lean), `own_sendings_at_value` (E2E/OfflineOwnSendingsAtValue.lean),
`trees_own_at_run` (E2E/OfflineOwnTreesAtRun.lean) and `keyFits_of_relation` (E2E/OfflineOwnKeyFits.lean).

Limits. In scope. `OwnRunsSay` is a premise: no member of it is given here; it reads the input and the carried coins: no later
law may take it as a hypothesis on a run and then speak of the coins as sampled anew. Nothing on completeness, on
soundness or on what is hidden.
-/
import E2E.OfflineOwnOwedCounted
import E2E.OfflineOwnSendingsAtValue
import E2E.OfflineRowsByPlace
import E2E.OfflineOwnTreesAtRun
import E2E.OfflineOwnKeyFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.Term
open OnBytes (TableKey)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Key (Xi descriptionFromSource)
open AtPublicFiles.KeyFile (randK14 keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub ownTestPlace)
open AtPublicFiles.KeyValues (batchedRowsSending indexMaskSending)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (jobKWAt)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open AtPublicFiles.AtFiles.Full (QK)
open VerifierAndGoals (PublicFiles InScope)
open H2K.Member (piKWFull codesKeyFull)

variable {files : PublicFiles}

/-- **The job that the offline prover's senders lay at the own test.** -/
abbrev ownManyAt (d : OfflineDescription) : ManyJob (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit :=
  jobKWAt d.source d.numbers d.later (indexMaskSending d.source) (batchedRowsSending matrixReader d.source d.numbers)
    ⟨parKey d.source d.later, 0⟩ id
    (askOf ⟨parKey d.source d.later, 0⟩ (fun w => matrixReader w.w₀)
      fun w => randK14 (tableCoins files w.rc 0))

/-- The same as a test's job. -/
abbrev ownJobAt (d : OfflineDescription) : TestJob (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) Unit :=
  (ownManyAt (files := files) d).toRun.toTest

section
variable (d : OfflineDescription) (S : OfflineSimulators)
  (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
    Unit Unit Unit)
  (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
  (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit)

/-- **THE NAMED PREMISE ON THE RUNS.** -/
def OwnRunsSay : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ r, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r →
    SayAtRun (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Xi Unit) (ownJobAt (files := files) d) (plainMany (ownManyAt (files := files) d)) k 2
      placeW r.called (midAtW F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ)

/-- **What is owed at the own test's row, at every returned run.** -/
theorem owedLastAt_own (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hsim : S.ownTest = [firstSim (simOwnKey d.source d.numbers d.later),
      restSim (simOwnKey d.source d.numbers d.later)])
    (hon : (c.second ownTestPlace).atPart = OnOwnTestEntry Face.own (ownJobAt (files := files) d)
      (simOwnKey d.source d.numbers d.later) codesKeyFull 2 piKWFull.nums.first)
    (hpos : (c.second ownTestPlace).positions = budBoth (simOwnKey d.source d.numbers d.later))
    (hfits : ∀ w₀ rc x, Rel w₀ rc x → keyFits x.key QK.par.S.fold.index = true)
    (hsay : OwnRunsSay (files := files) d S c Rel H) :
    OwedLastAt (files := files) d S c Rel H ownTestPlace := by
  intro w₀ rc x hrel k ρ r hρ hsil hrun
  obtain ⟨hI, hW, hO⟩ := own_sendings_at_value (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles files).EncodingRandomness) d.source d.numbers
    d.later matrixReader hs scope
  have hP : (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.prover H =
      { H with first := (keyProver (senderValue (files := files) d)).first,
               shared := (keyProver (senderValue (files := files) d)).shared,
               second := (keyProver (senderValue (files := files) d)).second } := by
    rw [prover_mute]
    exact offlineRows_prover_at _ _ _ _ _ H
  have hT := trees_own_at_run scope hs hK (offlineBook_eq hK) (senderValue (files := files) d)
    (senderValue_atAll (files := files) hs scope) matrixReader rfl rfl rfl rfl
    (P := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.prover H) (by rw [hP]) (by rw [hP])
    (by rw [hP]) hρ hrun (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
  exact owedAt_own_counted scope hs hK (offlineBook_eq hK) (senderValue (files := files) d) _ _ _ _
    rfl S c hsim hon hpos H hρ hrun (hfits w₀ rc x hrel) hI hW hO
    (hsay w₀ rc x hrel k ρ r hρ hsil hrun) hT

/-- **The same at a relation whose writing map writes the key of the sample.** -/
theorem owedLastAt_own_rel {X Seed Ans : Type} (ans : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → Seed → Ans)
    (Ryes : FullSizeMatrix → X → Prop) (wr : X × (Seed × Ans) → AtPublicFiles.KeyFile.KeyInst)
    (hwr : ∀ a, ∃ rec : OnBytes.Flat.RecFull, wr a = VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample rec)
    (hs : KeySourced files d.source d.numbers d.later)
    (scope : InScope files = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hsim : S.ownTest = [firstSim (simOwnKey d.source d.numbers d.later),
      restSim (simOwnKey d.source d.numbers d.later)])
    (hon : (c.second ownTestPlace).atPart = OnOwnTestEntry Face.own (ownJobAt (files := files) d)
      (simOwnKey d.source d.numbers d.later) codesKeyFull 2 piKWFull.nums.first)
    (hpos : (c.second ownTestPlace).positions = budBoth (simOwnKey d.source d.numbers d.later))
    (hsay : OwnRunsSay (files := files) d S c (relAt ans Ryes wr) H) :
    OwedLastAt (files := files) d S c (relAt ans Ryes wr) H ownTestPlace :=
  owedLastAt_own d S c (relAt ans Ryes wr) H hs scope hK hsim hon hpos
    (fun _ _ _ h => keyFits_of_relation ans Ryes wr hwr h) hsay

end

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.OwnRunsSay
#print axioms AtPublicFiles.OfflineRows.owedLastAt_own
#print axioms AtPublicFiles.OfflineRows.owedLastAt_own_rel
