-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnOnAtRun.lean: THE CONDITION OF THE KEY FILE's OWN PROXIMITY TEST's ROW (`OnOwnTestEntry`,
K12/Sim2/SlotOwnTest.lean) AT A RUN THAT HAS RETURNED, at each called part, at the run's own carried blocks, state and
front: in the form in which `owedAt_second_at` (E2E/OfflineOwedChains.lean) takes it: FROM TWO NAMED PREMISES ON THE RUN.
No family of invariants is read.

  `TreesAtRun`       the clause trees (`TreesAt`, K12/Sim2/Clauses.lean) at one run, at the called second part: a named premise
  `on_own_at_run`    the statement

The two. hsay: `SayAtRun` (E2E/OfflineSayAtRun.lean): the rows taken in hold at the job's words: the one clause of truth.
htrees: `TreesAtRun`: what the front lists of the three first trees are the job's own trees' columns: an identity between
the test's members and their senders, not a truth of the witness.
Paid here, at every called part: that the field holds columns; the five clauses on what was heard and seen; the door;
twelve of the thirteen clauses on the asks (`left_own_at_run`, E2E/OfflineOwnLeftAtRun.lean).

Other premises: those of `left_own_at_run`; hσ: the side is the seat of the pair behind the guard beside the simulators.

Limits. Both named premises read the input and the carried coins: no later law may take them as hypotheses on a run and
then speak of the coins as sampled anew. Nothing is said where a part was not called. Nothing on completeness, on
soundness or on what is hidden.
-/
import E2E.OfflineOwnLeftAtRun
import E2E.OfflineSayAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (SendPub Ask jobOmega)
open VerifiableInference.Desc (Block OpenedColumn FileDescription)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.KeyLay (pWK jobKWAt parIK parWK shapeOK)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK)
open H2K.Member (piKWFull codesKeyFull)

/-- **The clause trees at one run, at the called second part.** `front`: what the run shows in front of a part. -/
def TreesAtRun (V : Type) {W X : Type} (J : TestJob W X) (os : List (Fmt.Shape × Fmt.TreeSource))
    {Bk : ProverCoinCounts} (k : Coins Bk) (chain : ℕ) (a : VerifiableInference.Desc.Place)
    (called : Addr → Bool) (mid : Addr → Except ProofFile.Honest.Refusal (Option (ProofFile.Honest.Mid W X)))
    (front : Addr → Before) : Prop :=
  called ⟨a, 1⟩ = true → ∀ (m : ProofFile.Honest.Mid W X) (ca : CsAll (restPart J : Part V W X).carries),
    mid ⟨a, 1⟩ = .ok (some m) → carriedAt Bk k chain ⟨a, 1⟩ (restPart J : Part V W X) = .ok ca →
    TreesAt J chain os (stretches _ ca) m (front ⟨a, 1⟩)

section Run
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {W₀ Rc Ky X₀ Y : Type} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}

/-- **The row's condition at a called part of a returned run.** -/
theorem on_own_at_run (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
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
    (hsay : SayAtRun (Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask)
      (plainMany (jobKWAt Xs N Pl JI JW A id ask)) k 2 placeW r.called
      (midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ))
    (htrees : TreesAtRun (Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask) piKWFull.nums.first k 2
      placeW r.called (midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ)
      (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)))
    (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y
      Xi)
    (hσ : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder placeW
      (guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl))) [] = some σ)
    (u : Member (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y Xi) (hu : u ∈ σ.members)
    (hc : r.called ⟨placeW, u.number⟩ = true) (ca : CsAll u.part.carries)
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y)
    (hca : carriedAt Bk k 2 ⟨placeW, u.number⟩ u.part = .ok ca)
    (hmid : orRefused (midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ ⟨placeW, u.number⟩) = .ok m) :
    OnOwnTestEntry Face.own (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl) codesKeyFull 2
      piKWFull.nums.first u ca m
      (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨placeW, u.number⟩) := by
  have hp := own_sourced hS scope
  have hJ : (jobOwnKey Xs N Pl JI JW A ask).p = piKWFull := hp
  have hPW : (jobOwnKey Xs N Pl JI JW A ask).p.place = placeW := by
    rw [hJ]
    exact place_KW
  have hσ' : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder (jobOwnKey Xs N Pl JI JW A ask).p.place
      (guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl))) [] = some σ := by
    rw [hPW]
    exact hσ
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_own_key (Xs := Xs) (N := N) (Pl := Pl)
    (jobOwnKey Xs N Pl JI JW A ask) rfl (by rw [hp]; exact place_KW)
  have F : PlaceFacts (jobOwnKey Xs N Pl JI JW A ask).p dsKW := by
    rw [hJ]
    exact facts_KWFull
  have hrest : restLen (jobOwnKey Xs N Pl JI JW A ask).p.nums.stages ≠ 0 := by
    rw [hJ]
    exact rest_KW_pos
  obtain ⟨b₀, hb₀, e₀⟩ := Option.map_eq_some_iff.1 hσ'
  obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hf)
  have hpl : σ.block.place = placeW := by
    rw [← e₀]
    exact hbp.trans hPW
  have hg' : (P.second.find? fun g => g.place == σ.block.place) =
      some ((proverSideOfProximityTest (jobOwnKey Xs N Pl JI JW A ask) :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField) := by
    rw [hpl]
    exact hg
  have hbare : testSide (V := Local W₀ Rc Xi Unit) (keyFileDescription Xs N Pl).second.blocksInOrder
      (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl) [] =
      some (⟨b₀, testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl),
        fallOf [] (jobOwnKey Xs N Pl JI JW A ask).p.place⟩ :
        Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y
          Xi) := by
    unfold testSide Side.seated
    show Option.map _ ((keyFileDescription Xs N Pl).second.blocksInOrder.find? fun b => b.place == _) = _
    rw [hb₀]
    rfl
  obtain ⟨-, -, hall⟩ := any_at_place (V := Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask)
    (simOwnKey Xs N Pl) F _ b₀ hf hbp hr hor rfl hJ.symm rfl
  obtain ⟨hfit₀, hmem₀, -⟩ := hall [] _ hbare
  have hmem : σ.members = [(firstMember (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).guarded,
      (restMember (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).guarded] := by
    rw [← e₀]
    show membersOf (guardRow _) 0 _ = _
    rw [membersOf_guardRow]
    exact congrArg (List.map Member.guarded) hmem₀
  have hrowσ : σ.row = guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)) := by
    rw [← e₀]
  have hblk : σ.block ∈ (keyFileDescription Xs N Pl).second.blocksInOrder := by
    rw [← e₀]
    exact List.mem_of_find?_eq_some hb₀
  have hfitg : σ.fits = true := by
    rw [← e₀]
    show (⟨b₀, guardRow _, _⟩ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Y Xi).fits = true
    rw [fits_guarded_row]
    exact hfit₀
  rw [hmem] at hu
  have hc' : r.called ⟨σ.block.place, u.number⟩ = true := by
    rw [hpl]
    exact hc
  rcases List.mem_cons.1 hu with rfl | hu'
  · -- the first part: the field holds columns
    have hpos₁ : (firstMember (V := Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask)
        (simOwnKey Xs N Pl)).guarded.part.moves.length ≠ 0 := by
      show (firstPart (jobOwnKey Xs N Pl JI JW A ask) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField.moves.length ≠ 0
      rw [needsField_length, ProofFile.Honest.K12.Light.first_moves_len, hJ]
      exact first_KW_pos
    obtain ⟨pre, t, S₀⟩ := stands_member_last hS.named.plan hR σ hblk hfitg _
      (by rw [hmem]; exact List.mem_cons_self) hpos₁ _ hg' (by rw [hrowσ]; rfl)
    obtain ⟨m₂, e₁, e₂, v₀, s, cols, tr, hm₂, -, -, hop, -⟩ :=
      door_last_with_columns hS.named.plan hR σ _ pre t _ S₀ hrun hc'
    rw [hpl] at hm₂
    rw [hm₂] at hmid
    obtain rfl : m₂ = m :=
      Except.ok.inj (show (Except.ok m₂ : Except ProofFile.Honest.Refusal _) = .ok m from hmid)
    exact ⟨⟨_, hop⟩, fun hn => by cases hn⟩
  obtain rfl := List.mem_singleton.1 hu'
  have hc₁ : r.called ⟨σ.block.place, 1⟩ = true := hc'
  have hc₂ : r.called ⟨placeW, 1⟩ = true := hc
  obtain ⟨pre, t, c, m₁, S, hm₁, hca₁, hin₁, F5⟩ := five_at_test₃ hS.named.plan hρ hR
    (jobOwnKey Xs N Pl JI JW A ask) F _ rfl
    (fun s w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh) (simOwnKey Xs N Pl) hJ.symm rfl [] σ
    hσ' b₀ hf hbp hr hor hg' (by rw [hPW]; exact hT) hrun hc₁ hrest
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  obtain ⟨m₂, cs, hm₂, hop, hx, hdoor⟩ := door_at_last_any hS.named.plan hR hrun enterOwn placeW
    (jobOwnKey Xs N Pl JI JW A ask) rfl σ _ pre t S hc' hpl
  obtain rfl : m₁ = m₂ := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm₂))
  rw [hpl] at hm₁ hca₁ F5 hdoor
  have hmid₂ : orRefused (midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ ⟨placeW, 1⟩) = .ok m := hmid
  rw [hm₁] at hmid₂
  obtain rfl : m₁ = m :=
    Except.ok.inj (show (Except.ok m₁ : Except ProofFile.Honest.Refusal _) = .ok m from hmid₂)
  have hcaG : carriedAt Bk k 2 ⟨placeW, 1⟩ (restMember (V := Local W₀ Rc Xi Unit)
      (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).part = .ok ca :=
    (carriedAt_guarded _ _ _ _ _).symm.trans hca
  obtain rfl : c.2.1.2.2 = ca := Except.ok.inj (hca₁.symm.trans hcaG)
  have hleft := left_own_at_run scope hS hρ hR hrun JI JW A ask hkey hI hW hO hg hT hc₂ m₁ hm₁
    (stretches _ c.2.1.2.2) (hsay hc₂ m₁ _ hm₁ hcaG)
  refine ⟨⟨_, hop⟩, onEntry_of_free Face.own _ _ _ 2 _ _ _ m₁ _ ?_⟩
  refine ⟨F5.le, F5.leS, F5.heardFit, F5.heard, ?_, F5.fold, hleft, htrees hc₂ m₁ _ hm₁ hcaG⟩
  show _ = stateAtOwnKey Xs N Pl m₁.st.input.x _
  rw [hx]
  exact hdoor

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.TreesAtRun
#print axioms AtPublicFiles.OfflineRows.on_own_at_run
