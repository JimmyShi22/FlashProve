-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFoldedPaid.lean: the offline file's row of the proximity test on G_u (place ⟨2, –, 9⟩ of the key file's shared chain): onAtRun_folded_key
(Johnson/Desc/ProofFile/Honest/K12/Sim2/RowFoldedPub.lean) with six of its premises paid at the key file's prover: hb8, hr0, hr1 (the plan's eight
sub-protocols and the roots in front of the two sendings: eight_sourced, roots_sourced, …/K12/Sim2/RowFoldedEight.lean) and hg, hgU, hgO (the filling).

  shared_nodup', sends_found, folded_found   the prover's shared list finds the two sendings' halves and the test's half at their places
  foldedJob, foldedSim   the test's job at the senders' own letters (K.send, bsOf K, stOf K, wtOf K, rdOf K: what onUOf, E2E/KeyPartsHalves.lean, hands the
                    half), and the simulators' job beside it
  onAtRun_folded_paid   THE STATEMENT: OnAtRun₂ T ρ r L at the list of the test on G_u

What stays. hleft : where the second part was called, LeftAtFolded at the run's own state and carried blocks: the two clauses on the asks; one of its fourteen
sentences, allSay, is on hidden data. Of what the rule hands to hleft (the side, where it stands, InsideOf at T's invariant, what was seen, the call, the state,
the carried blocks, the front) this form keeps the call, the state and the carried blocks. The row's letters hplace, hrow, hOn. T : ThreadsP, a letter. Two
ties of the sides' prover to keyProver K (hsh, hst) and four equations on K (hsend, hsp, hU, hOp). KeySourced, InScope, fullPub = some K₀.
Limits. The rule moves the debt and pays none of it. Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFoldedEight
import Johnson.SendSim.Seat.LotsGuardTie
import E2E.KeyPartsHalves
import E2E.KeyShapeSharedTies
import E2E.KeyValueHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows.Folded
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (SendPub sendPlace jobU jobOmega sendingPart liftSend)
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces sharedPar beforeSharedPoint)
open H2K.Member (codesKeyFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (jobKU proverSideOfTestOnU bsOf stOf wtOf rdOf)
open AtPublicFiles.KeyValueHolds (place_p12At)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-! ## 1 The filling -/

section Filling
variable {W₀ Rc X₀ Y Wk : Type} (K : KeyParts W₀ Rc X₀ Y Wk)

/-- No two halves of the prover's shared list stand at one place. -/
theorem shared_nodup' (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hO : K.onOmega.place = omegaTestPlace) : ((keyProver K).shared.map (·.place)).Nodup := by
  rw [keyProver_shared K hsp, hU, hO]
  decide

/-- **The prover's shared list finds the two sendings' halves at their places**, at the senders' own readers. -/
theorem sends_found (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hO : K.onOmega.place = omegaTestPlace) :
    ((keyProver K).shared.find? fun g => g.place == sendPlace 2) = some ⟨sendPlace 2,
        [(liftSend (askOf K.send (wtOf K) (rdOf K)) (sendingPart (jobU K.send)) :
          Part Empty (Common W₀ Rc TableKey) X₀)]⟩ ∧
      ((keyProver K).shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
        [(liftSend (askOf K.send (wtOf K) (rdOf K)) (sendingPart (jobOmega K.send)) :
          Part Empty (Common W₀ Rc TableKey) X₀)]⟩ := by
  have hn := shared_nodup' K hsp hU hO
  have m2 : (⟨sendPlace 2, [(liftSend (askOf K.send (wtOf K) (rdOf K)) (sendingPart (jobU K.send)) :
      Part Empty (Common W₀ Rc TableKey) X₀)]⟩ : Placed Empty (Common W₀ Rc TableKey) X₀) ∈
      (keyProver K).shared :=
    List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m5 : (⟨sendPlace 5, [(liftSend (askOf K.send (wtOf K) (rdOf K))
      (sendingPart (jobOmega K.send)) : Part Empty (Common W₀ Rc TableKey) X₀)]⟩ :
      Placed Empty (Common W₀ Rc TableKey) X₀) ∈ (keyProver K).shared :=
    List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  exact ⟨OnBytes.SendSim.Seat.find_of_nodup
      (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place) _ hn _ m2,
    OnBytes.SendSim.Seat.find_of_nodup
      (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place) _ hn _ m5⟩

/-- **It finds the letter onU at the test's place.** -/
theorem folded_found (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hO : K.onOmega.place = omegaTestPlace) :
    ((keyProver K).shared.find? fun g => g.place == foldedTestPlace) = some K.onU := by
  have f : ((keyProver K).shared.find? fun g => g.place == K.onU.place) = some K.onU :=
    OnBytes.SendSim.Seat.find_of_nodup
      (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place) _ (shared_nodup' K hsp hU hO) K.onU
      (List.mem_append_right _ List.mem_cons_self)
  rw [hU] at f
  exact f

end Filling

/-! ## 2 The statement -/

section Paid
variable {W₀ Rc X₀ Y Wk : Type}

/-- The job of the test on G_u at the senders' own letters. -/
abbrev foldedJob (K : KeyParts W₀ Rc X₀ Y Wk) (Pl : LaterPlaces) : TestJob (Common W₀ Rc TableKey) X₀ :=
  (jobKU (X := X₀) K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K)).toRun.toTest

/-- The simulators' job beside it. -/
abbrev foldedSim (K : KeyParts W₀ Rc X₀ Y Wk) (Pl : LaterPlaces) : SimJob TableKey :=
  simLocU K.send.P (sentOf K.send.P.S) (bsOf K) (pKU Pl) 1

/-- **The clause of the rule at the list of the test on G_u, at the key file's prover: hleft alone is left of the condition.** -/
theorem onAtRun_folded_paid (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ Y Wk) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfTestOnU K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))
    (hOp : K.onOmega.place = omegaTestPlace)
    {H : Prover W₀ Rc Xi TableKey Unit X₀ Y}
    {G : Sides (keyFileDescription Xs N Pl) (keyBook K₀) W₀ Rc TableKey Unit X₀ Y}
    (hsh : (G.prover H).shared = (keyProver K).shared) (hst : (G.prover H).storedWords = stOf K)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins (keyBook K₀)} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k ρ = .ok r)
    (L : Lettered (keyBook K₀) (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀
      TableKey)
    (hplace : L.place = (pKU Pl).place)
    (hrow : L.row = testPairs (foldedJob K Pl) (foldedSim K Pl))
    (hOn : L.On = OnEntry Face.shared (foldedJob K Pl) (foldedSim K Pl) codesKeyFull 1
      (pKU Pl).nums.first)
    (hleft : r.called ⟨L.place, 1⟩ = true → ∀ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (ca : CsAll (restMember (V := Empty) (foldedJob K Pl) (foldedSim K Pl)).part.carries),
      midSharedAtW (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      carriedAt (keyBook K₀) k 1 ⟨L.place, 1⟩
        (restMember (V := Empty) (foldedJob K Pl) (foldedSim K Pl)).part = .ok ca →
      LeftAtFolded (foldedJob K Pl) codesKeyFull (pKU Pl).nums.first (stretches _ ca) m) :
    OnAtRun₂ T ρ r L := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb8⟩ := eight_sourced scope hS
  obtain ⟨hr0, hr1⟩ := roots_sourced scope hS b1 b2 b3 b4 b5 b6 b7 b8 hb8
  have ebs : bsOf K = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold bsOf
    rw [hsend]
    show (Desc.K14.blocks (parKey Xs Pl)).getD [] = _
    rw [hb8]
    rfl
  have hUp : K.onU.place = foldedTestPlace := by
    rw [hU]
    exact place_p12At _ _
  have hpt : (pKU Pl).place = foldedTestPlace := H2K.JointK.place_of_p12At _ _
  obtain ⟨f2, f5⟩ := sends_found K hsp hUp hOp
  have fU := folded_found K hsp hUp hOp
  rw [hU] at fU
  rw [← hsh] at f2 f5 fU
  rw [← hpt] at fU
  unfold proverSideOfTestOnU at fU
  simp only [foldedJob, foldedSim] at hrow hOn hleft
  rw [ebs, ← hst, hsend] at hrow hOn hleft fU
  rw [hsend] at f2 f5
  exact onAtRun_folded_key scope hS hK T hρ hR hrun b1 b2 b3 b4 b5 b6 b7 b8 hb8 hr0 hr1 (wtOf K) (rdOf K)
    L hplace hrow hOn fU f2 f5 fun m ca _ _ _ _ _ _ hc hm hca _ => hleft hc m ca hm hca

end Paid

end AtPublicFiles.OfflineRows.Folded

#print axioms AtPublicFiles.OfflineRows.Folded.shared_nodup'
#print axioms AtPublicFiles.OfflineRows.Folded.sends_found
#print axioms AtPublicFiles.OfflineRows.Folded.folded_found
#print axioms AtPublicFiles.OfflineRows.Folded.onAtRun_folded_paid
