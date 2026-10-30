-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnOwed.lean: WHAT IS OWED AT A RUN (`Lettered.owedAt`, Johnson/Desc/ProofFile/Honest/Rule.lean) AT THE OFFLINE
FILE's ROW OF THE OWN PROXIMITY TEST, the last chain's one row, FROM THREE NAMED PREMISES ON THE RUN. At the rows
`offlineRows` (E2E/OfflineSides.lean), muted, of any senders K whose field `own` is the pair behind the guard. In scope, at
the written book.

  `own_row_is`       the last chain's one row: its place, pairs, condition and `bud`
  `ties_at_own`      the book's ties at the test's place and the job's number of members
  `owedAt_own`       the statement

The three. hsay: `SayAtRun` (E2E/OfflineSayAtRun.lean): the one clause of truth. htrees: `TreesAtRun`
(E2E/OfflineOwnOnAtRun.lean): the front's columns of the three first trees are the job's. hbud: the row's `bud` at the run's own
challenges and positions: a count.
What is laid at the place: hsim: the two simulators beside the pair. hon: the row's condition is `OnOwnTestEntry` at the job.

By `owedAt_second_at` (E2E/OfflineOwedChains.lean) and `on_own_at_run` (E2E/OfflineOwnOnAtRun.lean).

Limits. Those of `on_own_at_run`. Other premises: KeySourced, InScope, the written sizes and book; the challenges fit; the
run has returned; hkey, hI, hW, hO. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineOwnOnAtRun
import E2E.OfflineOwedChains
import E2E.OfflineSides
import E2E.OfflineRunsOwn
import E2E.KeyOwnAgree
import E2E.KeyBookThirdNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (SendPub Ask jobOmega)
open OnBytes (TableKey)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub ownTestPlace)
open AtPublicFiles.KeyLay (pWK jobKWAt proverSideOfGuardedSending parIK parWK shapeOK)
open AtPublicFiles.KeyLastChain (ties_own place_W members_own)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK)
open H2K.Member (piKWFull codesKeyFull)

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ Y Wk : Type}

/-- The book's ties at the own test's place, at the job's number of members. -/
theorem ties_at_own {K₀ : KeyPub} (hK₀ : fullPub = some K₀)
    (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub) (ask : Local W₀ Rc Xi Unit → Ask) :
    tiesB (keyBook K₀) placeW (jobOwnKey Xs N Pl JI JW A ask).members.length = true := by
  have h := ties_own K₀ hK₀
  rw [← place_W, ← members_own Xs N Pl JI JW A id ask] at h
  exact h

/-- **The last chain's one row**: its place, its pairs, its condition and its `bud`. -/
theorem own_row_is (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc X₀ Y Wk) (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub)
    (ask : Local W₀ Rc Xi Unit → Ask) (hown : K.own = proverSideOfGuardedSending Xs N Pl JI JW A id ask)
    (S : OfflineSimulators) (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y)
    (hsim : S.ownTest = [firstSim (simOwnKey Xs N Pl), restSim (simOwnKey Xs N Pl)]) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.second, L.place = ownTestPlace ∧
      L.row = guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)) ∧ L.On = (c.second ownTestPlace).atPart ∧
      L.bud = (c.second ownTestPlace).positions := by
  intro L hL
  have hplace : K.own.place = ownTestPlace := by
    rw [hown]
    show (pWK Pl).place = _
    rw [own_sourced hS scope]
    exact place_KW
  have hL' : L ∈ ((rowsAt (Cl := (keyFileDescription Xs N Pl).Cl) S.byChain.second c.second [K.own]).map
      Lettered.mute) := hL
  unfold rowsAt at hL'
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hL'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL']
    exact hplace
  · rw [hL']
    show partsBeside K.own.parts (S.byChain.second K.own.place) = _
    rw [hplace, hown]
    show partsBeside _ S.ownTest = _
    rw [hsim]
    rfl
  · rw [hL']
    show (c.second K.own.place).atPart = _
    rw [hplace]
  · rw [hL']
    show (c.second K.own.place).positions = _
    rw [hplace]

/-- **What is owed at a returned run at the own test's row.** -/
theorem owedAt_own (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK₀ : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc X₀ Y Wk)
    (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub) (ask : Local W₀ Rc Xi Unit → Ask)
    (hown : K.own = proverSideOfGuardedSending Xs N Pl JI JW A id ask) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y)
    (hsim : S.ownTest = [firstSim (simOwnKey Xs N Pl), restSim (simOwnKey Xs N Pl)])
    (hon : (c.second ownTestPlace).atPart =
      OnOwnTestEntry Face.own (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl) codesKeyFull 2 piKWFull.nums.first)
    (H : Prover W₀ Rc KeyInst TableKey Unit X₀ Y) {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)} (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hrun : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc
      x k ρ = .ok r)
    (hkey : keyFits ((descriptionFromSource Xs N Pl).pub x).key QK.par.S.fold.index = true)
    (hI : JI.P.sent = parIK.sent) (hW : JW.P.sent = parWK.sent)
    (hO : ∀ n, ((jobOmega ⟨A.P, n + A.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK)
    (hsay : SayAtRun (Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask) (plainMany (jobKWAt Xs N Pl JI JW A id ask)) k 2 placeW
      r.called (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H)
        w₀ rc x k ρ))
    (htrees : TreesAtRun (Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask) piKWFull.nums.first k 2 placeW r.called
      (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k
        ρ)
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)))
    (hbud : ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.second,
      ∀ σ, L.side (keyFileDescription Xs N Pl).second.blocksInOrder = some σ → ∀ u ∈ σ.members,
        L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.second, L.place = ownTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).second.blocksInOrder k 2
        (fun a => orRefused (midAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  intro L hL _
  obtain ⟨eP, eR, eO₀, eB⟩ := own_row_is scope hS K JI JW A ask hown S c hsim L hL
  have eO := eO₀.trans hon
  have hsec : ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H).second =
      (keyProver K).second := by
    rw [prover_mute, offlineRows_prover_at]
  have hst : ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H).storedWords =
      H.storedWords := by
    rw [prover_mute, offlineRows_prover_at]
    rfl
  have hg : (((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H).second.find? fun g =>
      g.place == placeW) = some ((proverSideOfProximityTest (jobOwnKey Xs N Pl JI JW A ask) :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField) := by
    rw [hsec]
    have q := find_own K hown
    rw [own_sourced hS scope, place_KW] at q
    exact q
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts hrun
  have book : Bk.word (keyFileDescription Xs N Pl) = none := by
    rw [hB]
    exact AtPublicFiles.KeyBook.book_passes scope hS.named K₀ hK₀
  have hT : tiesB Bk placeW (jobOwnKey Xs N Pl JI JW A ask).members.length = true := by
    rw [hB]
    exact ties_at_own hK₀ JI JW A ask
  refine owedAt_second_at hS.named.plan book hrun hL _ (fun σ hσ u hu hc ca m hca hm => ?_)
    (hbud L hL)
  · rw [eO]
    rw [eP] at hc hca hm ⊢
    have hσ' : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder placeW (guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl))) [] =
        some σ := by
      have q : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder L.place L.row [] = some σ := hσ
      rw [eP, eR] at q
      exact q
    have e := on_own_at_run scope hS hρ hR hrun JI JW A ask hkey hI hW hO hg hT hsay
      (by rw [hst]; exact htrees) σ hσ' u hu hc ca m hca hm
    rw [hst] at e
    exact e

end

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.own_row_is
#print axioms AtPublicFiles.OfflineRows.ties_at_own
#print axioms AtPublicFiles.OfflineRows.owedAt_own
