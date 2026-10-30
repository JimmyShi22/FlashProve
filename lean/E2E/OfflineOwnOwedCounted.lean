-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnOwedCounted.lean: E2E/OfflineOwnOwed.lean's statement WITH THE COUNT PAID: what is owed at a returned run at the
offline file's row of the own proximity test, FROM TWO NAMED PREMISES ON THE RUN: `SayAtRun` (the one clause of truth) and
`TreesAtRun` (the front's columns of the three first trees are the job's).

  `bud_own_at_run`        the row's `bud` at the run's own challenges and positions, where it is `budBoth` of the simulators' job:
                        by `budOwed₃_guarded_KW` (Johnson/M1/KeyBudWG.lean) and `second_part_at_run` (E2E/OfflineOwedChains.lean)
  `owedAt_own_counted`    the statement

What is laid at the place: hsim, hon as in E2E/OfflineOwnOwed.lean; hpos: the row's `bud` is `budBoth`.

Limits. Those of E2E/OfflineOwnOwed.lean. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineOwnOwed
import Johnson.M1.KeyBudWG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (SendPub Ask jobOmega)
open OnBytes (TableKey)
open OnBytes.M1.KeyBud (budOwed₃_guarded_KW)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub ownTestPlace)
open AtPublicFiles.KeyLay (pWK jobKWAt proverSideOfGuardedSending parIK parWK shapeOK)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK)
open H2K.Member (piKWFull codesKeyFull)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ Y Wk : Type}

/-- **The row's `bud` at the run's own challenges and positions.** -/
theorem bud_own_at_run (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK₀ : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc X₀ Y Wk)
    (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub) (ask : Local W₀ Rc Xi Unit → Ask)
    (hown : K.own = proverSideOfGuardedSending Xs N Pl JI JW A id ask) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y)
    (hsim : S.ownTest = [firstSim (simOwnKey Xs N Pl), restSim (simOwnKey Xs N Pl)])
    (hpos : (c.second ownTestPlace).positions = budBoth (simOwnKey Xs N Pl))
    (H : Prover W₀ Rc KeyInst TableKey Unit X₀ Y) {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)} (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hrun : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc
      x k ρ = .ok r) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.second,
      ∀ σ, L.side (keyFileDescription Xs N Pl).second.blocksInOrder = some σ → ∀ u ∈ σ.members,
        L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩) := by
  intro L hL σ hσ u hu
  obtain ⟨eP, eR, -, eB⟩ := own_row_is scope hS K JI JW A ask hown S c hsim L hL
  have hp := own_sourced hS scope
  have hJ : (jobOwnKey Xs N Pl JI JW A ask).p = piKWFull := hp
  have hPW : (jobOwnKey Xs N Pl JI JW A ask).p.place = ownTestPlace := by
    rw [hJ]
    exact place_KW
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_own_key (Xs := Xs) (N := N) (Pl := Pl)
    (jobOwnKey Xs N Pl JI JW A ask) rfl (by rw [hp]; exact place_KW)
  have F : PlaceFacts (jobOwnKey Xs N Pl JI JW A ask).p dsKW := by
    rw [hJ]
    exact facts_KWFull
  have book : Bk.word (keyFileDescription Xs N Pl) = none := by
    rw [hB]
    exact AtPublicFiles.KeyBook.book_passes scope hS.named K₀ hK₀
  obtain ⟨-, ⟨pre, t, hcut, hd, ha⟩, -⟩ := second_part_at_run hS.named.plan book hrun hL hσ hu
  rw [hd, ha]
  exact budOwed₃_guarded_KW scope hS.named L (jobOwnKey Xs N Pl JI JW A ask) F (by rw [hJ]) hPW hf hbp hr hor rfl (simOwnKey Xs N Pl) hJ.symm rfl
    (eP.trans hPW.symm) eR (fun n ds asks h => by rw [eB, hpos]; exact h) σ hσ u hu pre t _ hcut rfl
    ρ hρ

/-- **What is owed at a returned run at the own test's row, the count paid.** -/
theorem owedAt_own_counted (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    {K₀ : KeyPub} (hK₀ : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (K : KeyParts W₀ Rc X₀ Y Wk) (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub)
    (ask : Local W₀ Rc Xi Unit → Ask) (hown : K.own = proverSideOfGuardedSending Xs N Pl JI JW A id ask)
    (S : OfflineSimulators) (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y)
    (hsim : S.ownTest = [firstSim (simOwnKey Xs N Pl), restSim (simOwnKey Xs N Pl)])
    (hon : (c.second ownTestPlace).atPart =
      OnOwnTestEntry Face.own (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl) codesKeyFull 2 piKWFull.nums.first)
    (hpos : (c.second ownTestPlace).positions = budBoth (simOwnKey Xs N Pl))
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
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked))) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.second, L.place = ownTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).second.blocksInOrder k 2
        (fun a => orRefused (midAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called :=
  owedAt_own scope hS hK₀ hB K JI JW A ask hown S c hsim hon H hρ hrun hkey hI hW hO hsay htrees
    (bud_own_at_run scope hS hK₀ hB K JI JW A ask hown S c hsim hpos H hρ hrun)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.bud_own_at_run
#print axioms AtPublicFiles.OfflineRows.owedAt_own_counted
