-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnLeftAtRun.lean: AT A RUN THAT HAS RETURNED, WHERE THE SECOND PART OF THE KEY FILE's OWN PROXIMITY TEST WAS
CALLED: what is left of the condition at that part's entry (`LeftAtOwnKey`, K12/Sim2/RowOwnKeyAtRun.lean: the two clauses
on the asks) follows from ONE of its thirteen clauses, said in front of the test (`SayInFront`, E2E/OfflineOwnFolds.lean:
the rows taken in hold at the job's words). No thread, no stand, no truth of the witness beyond that premise.

  `doorAt_of_run`      a run whose two earlier chains ended in a verifier's state folds them as the description does
                     (`DoorAt`, E2E/KeyLastSaid.lean): by `runC_ends`, `fold_some` (Honest/Law/RunC.lean)
  `reached_at_run`     at a called part of the own test, behind the first part's rounds: the job's state on entry, at the
                     input and the front as the second part lays it, is the seat's way in at a state that the
                     description's accepted folds reach (`ReachedOwn`)
  `left_own_at_run`    the statement

Premises of `left_own_at_run`. In scope. hρ, hR, hrun: the challenges fit, `ready` and `runC` have returned. hkey: the
instance's key has the written sizes. hI, hW, hO: what the three sendings send. hg: the prover's side at the place is
the pair behind the guard. hT: the book's ties. hc: the second part was called. hm: m is the walk's state there. hsay.
The stretches mem are free: the clauses on the shape and on the form hold at every family of coins.

Limits. It moves twelve clauses off the debt and leaves the thirteenth. `SayInFront` reads the input and the carried
coins: no later law may take it as a hypothesis on a run and then speak of the coins as sampled anew. The clause trees
of the same condition is not treated here. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineOwnFolds
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowOwnKeyAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (SendPub Ask jobOmega)
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks withEmptySealRound)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.KeyLay (pWK jobKWAt parIK parWK shapeOK)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyLastChain (DoorAt pre_key formPub_KW)
open H2K.Member (piKWFull codesKeyFull)

/-- **A run whose two earlier chains ended in a verifier's state folds them as the description does.** -/
theorem doorAt_of_run {Xi' W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi'} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi' Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi'} {k : Coins Bk} {ρ : Draws}
    {r : RunC F} (hrun : runC F Bk P w₀ rc x k ρ = .ok r) {e₁ : F.S₁} {e₂ : F.S₂} {v₀ : F.S₃}
    (he₁ : r.ends.1 = some e₁) (he₂ : r.ends.2.1 = some e₂)
    (hst : F.start₃ (F.pub x) e₁ e₂ = .ok v₀) :
    DoorAt F x (withEmptySealRound r.run.views.1).rounds r.run.views.2.1.rounds r.run.views.1.opened
      r.run.views.2.1.opened e₁ e₂ v₀ := by
  obtain ⟨⟨g1, g2, g3⟩, ⟨g4, g5, g6⟩, -⟩ := runC_ends hrun
  exact ⟨g1, g4, g2, g5, (fold_some 0 _ _ e₁ _ _ g1 g2).1 (g3.symm.trans he₁),
    (fold_some 0 _ _ e₂ _ _ g4 g5).1 (g6.symm.trans he₂), hst⟩

section Run
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {W₀ Rc Ky X₀ Y : Type} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}

/-- **At a called part of the own test, behind the first part's rounds, the job's state on entry is the way in
at a reached state.** -/
theorem reached_at_run {V Pb : Type} (hpl : (keyFileDescription Xs N Pl).planOk = true)
    (hR : ready (keyFileDescription Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Local W₀ Rc Xi Unit) Y)
    (hJ : J.rec₀ = doorW (keyFileDescription Xs N Pl) (·.x) enterOwn placeW idleT12)
    (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V (Local W₀ Rc Xi Unit) Y Pb)
    (u : Member V (Local W₀ Rc Xi Unit) Y Pb)
    (pre t : List (Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl))
    (S : StandsAt (keyFileDescription Xs N Pl).second.blocksInOrder R.second σ u pre t (firstLen J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = placeW) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y) (s : S₃),
      midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      ReachedOwn Xs N Pl x s ∧ enterOwn s = .ok (J.rec₀ m.st.input (restFront J m)) := by
  obtain ⟨m, e₁, e₂, v₀, s, cols, tr, hm, hin, hlen, hop, he₁, he₂, hst, hfold, -, hd⟩ :=
    door_last_with_columns hpl hR σ u pre t _ S hrun hc
  have hn := (places_nodup (((keyFileDescription Xs N Pl).planOk_ok).1 hpl).places).2.2
  have hcut : (keyFileDescription Xs N Pl).second.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : (keyFileDescription Xs N Pl).second.blocksInOrder.takeWhile (·.place != placeW) = pre := by
    rw [← ha, hcut]
    exact Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')
  have hpre2 : pre = (descriptionFromSource Xs N Pl).second.blocksInOrder.take 2 := hpre.symm.trans (pre_key Xs N Pl)
  have hx : (fun w : Local W₀ Rc Xi Unit => w.x) m.st.input = x := by rw [hin]
  have hk : ((keyFileDescription Xs N Pl).first.blocksInOrder.flatMap (·.rounds)).length +
      ((keyFileDescription Xs N Pl).shared.blocksInOrder.flatMap (·.rounds)).length +
      (pre.flatMap (·.rounds)).length ≤ m.seen.length - firstLen J.p.nums.stages := by
    omega
  have hdoor := hd (fun w : Local W₀ Rc Xi Unit => w.x) m.st.input enterOwn (restFront J m)
    (m.seen.length - firstLen J.p.nums.stages) hx hk rfl rfl
  obtain ⟨t', ht'⟩ := enterOwn_returns s
  have hfold2 : foldBlocks (descriptionFromSource Xs N Pl).lastChainFirstTreeNumber ((descriptionFromSource Xs N Pl).second.blocksInOrder.take 2) v₀
      (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) := by
    rw [← hpre2]
    exact hfold
  refine ⟨m, s, hm, ⟨_, _, _, _, e₁, e₂, v₀, _, cols, doorAt_of_run hrun he₁ he₂ hst, hfold2⟩, ?_⟩
  · rw [ht', hJ]
    unfold doorW doorLast
    rw [hpre, hdoor, ht']
    rfl

/-- **What is left at the second part's entry, from the one clause on the words.** -/
theorem left_own_at_run (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub) (ask : Local W₀ Rc Xi Unit → Ask)
    (hkey : keyFits ((descriptionFromSource Xs N Pl).pub x).key QK.par.S.fold.index = true)
    (hI : JI.P.sent = parIK.sent) (hW : JW.P.sent = parWK.sent)
    (hO : ∀ n, ((jobOmega ⟨A.P, n + A.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK)
    (hg : (P.second.find? fun g => g.place == placeW) =
      some ((proverSideOfProximityTest (jobOwnKey Xs N Pl JI JW A ask) :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField))
    (hT : tiesB Bk placeW (jobOwnKey Xs N Pl JI JW A ask).members.length = true)
    (hc : r.called ⟨placeW, 1⟩ = true) (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y)
    (hm : midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ ⟨placeW, 1⟩ = .ok (some m))
    (mem : ℕ → ProofFile.Honest.K12.Stretch)
    (hsay : SayInFront (jobKWAt Xs N Pl JI JW A id ask) m.st.input
      (restFront (jobOwnKey Xs N Pl JI JW A ask) m)
      (carriedCoins (jobOwnKey Xs N Pl JI JW A ask) mem)) :
    LeftAtOwnKey (jobOwnKey Xs N Pl JI JW A ask) codesKeyFull piKWFull.nums.first mem m := by
  have hp := own_sourced hS scope
  have hJ : (jobOwnKey Xs N Pl JI JW A ask).p = piKWFull := hp
  have hPW : (jobOwnKey Xs N Pl JI JW A ask).p.place = placeW := by
    rw [hJ]
    exact place_KW
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_own_key (Xs := Xs) (N := N) (Pl := Pl)
    (jobOwnKey Xs N Pl JI JW A ask) rfl (by rw [hp]; exact place_KW)
  have F : PlaceFacts (jobOwnKey Xs N Pl JI JW A ask).p dsKW := by
    rw [hJ]
    exact facts_KWFull
  have hrest : restLen (jobOwnKey Xs N Pl JI JW A ask).p.nums.stages ≠ 0 := by
    rw [hJ]
    exact rest_KW_pos
  obtain ⟨σ, hσ, hσb⟩ : ∃ σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Y Xi,
      Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder (jobOwnKey Xs N Pl JI JW A ask).p.place
        (guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl))) [] = some σ ∧
      σ.block = b := by
    refine ⟨⟨b, guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)),
      fallOf [] (jobOwnKey Xs N Pl JI JW A ask).p.place⟩, ?_, rfl⟩
    unfold Side.seated
    show Option.map _ ((keyFileDescription Xs N Pl).second.blocksInOrder.find? fun b => b.place == _) = _
    rw [hf]
    rfl
  have hpl : σ.block.place = placeW := by rw [hσb, hbp, hPW]
  have hg' : (P.second.find? fun g => g.place == σ.block.place) =
      some ((proverSideOfProximityTest (jobOwnKey Xs N Pl JI JW A ask) :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField) := by
    rw [hpl]
    exact hg
  have hc₁ : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hpl]
    exact hc
  obtain ⟨pre, t, c, m₁, S, hm₁, -, -, F5⟩ := five_at_test₃ hS.named.plan hρ hR
    (jobOwnKey Xs N Pl JI JW A ask) F _ rfl
    (fun s w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh) (simOwnKey Xs N Pl) hJ.symm rfl [] σ
    hσ b hf hbp hr hor hg' (by rw [hPW]; exact hT) hrun hc₁ hrest []
  obtain ⟨m₂, s, hm₂, hreach, hen⟩ := reached_at_run hS.named.plan hR hrun
    (jobOwnKey Xs N Pl JI JW A ask) rfl σ _ pre t S hc₁ hpl
  obtain rfl : m₁ = m₂ := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm₂))
  rw [hpl] at hm₁
  obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm))
  have hasks := asks_reached JI JW A id ask hS scope hkey hI hW hO hreach m₁.st.input
    (restFront (jobOwnKey Xs N Pl JI JW A ask) m₁) hen
    (carriedCoins (jobOwnKey Xs N Pl JI JW A ask) mem) hsay
  obtain ⟨a, next, rest, hst⟩ :
      ∃ a next rest, (jobOwnKey Xs N Pl JI JW A ask).p.nums.stages = a :: next :: rest := by
    have hform := F.form
    unfold formPubB at hform
    cases hs' : (jobOwnKey Xs N Pl JI JW A ask).p.nums.stages with
    | nil => rw [hs'] at hform; cases hform
    | cons a l =>
      cases l with
      | nil => rw [hs'] at hform; cases hform
      | cons b' r' => exact ⟨a, b', r', rfl⟩
  have hleft := left_of_front (jobOwnKey Xs N Pl JI JW A ask) codesKeyFull 3 mem m₁ a next rest hst
    (by rw [hJ]; exact formPub_KW) F5.heardFit hasks
  obtain ⟨Dp, cc, Rw, h3, hA, hD⟩ := hleft
  exact ⟨Dp, cc, Rw, h3.trans first_KW_length.symm, hA, hD⟩

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.doorAt_of_run
#print axioms AtPublicFiles.OfflineRows.reached_at_run
#print axioms AtPublicFiles.OfflineRows.left_own_at_run
