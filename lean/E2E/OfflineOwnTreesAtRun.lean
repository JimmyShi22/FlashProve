-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnTreesAtRun.lean: THE CLAUSE TREES OF THE CONDITION AT THE KEY FILE's OWN PROXIMITY TEST (`TreesAtRun`,
E2E/OfflineOwnOnAtRun.lean) HOLDS AT EVERY RETURNED RUN of a prover whose three lists are `keyProver K`'s, at senders K whose index
masks' sending, sending of W and plan of the shared sendings are the description's own. In scope, at the written book.
What the front lists of the three first trees are the job's own trees' columns: an identity between the test's members
and their senders; no truth of the witness is read.

  `ownAsk`               the reader of Omega's input that the own test's job bears
  `plan_written`         the written plan's codes and shape: a kernel line
  `omega_found`          the prover's shared list finds Omega's sending at its place
  `trees_own_at_run`     the statement

By `own_trees_stand` (Johnson/Desc/ProofFile/Honest/K12/Sim2/RowOwnKeyPub.lean), whose named premises are paid here: the filling's three
finds (`first_finds`, E2E/OfflineRunsSendings.lean; `omega_found`); what the data of W's sending reads of a front
(`keyW_data_in_front`, E2E/OfflineKeyPointsInFront.lean); that Omega's input is the test's (by unfolding); the plans (`idx_plan`,
`w_plan` there; `plan_written`).

Limits. In scope. Nothing is said where the second part was not called. Nothing on completeness, on soundness or on what
is hidden.
-/
import E2E.OfflineOwnOwed
import E2E.OfflineKeyPointsInFront
import E2E.OfflineRunsSendings
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowOwnKeyPub
import Johnson.SendSim.Seat.LotsGuardTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (SendPub Ask jobOmega rowsOf liftSend sendingPart)
open OnBytes (TableKey)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver randK14)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub OneFull ownTestPlace omegaPlace idxPlace wPlace rideW)
open AtPublicFiles.KeyValues (batchedRowsSending indexMaskSending oneOf)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (pWK jobKWAt proverSideOfGuardedSending parIK parWK)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open H2K.Member (piKWFull codesKeyFull)

/-- The written plan's codes and shape are those of the written sendings. -/
theorem plan_written : QK.codes = AtPublicFiles.KeyLay.AK.P.codes ∧ QK.S = AtPublicFiles.KeyLay.AK.P.S := by
  refine ⟨?_, ?_⟩ <;> first | rfl | decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc Wk : Type}

/-- **The reader of Omega's input that the own test's job bears.** -/
abbrev ownAsk (K : KeyParts W₀ Rc Unit Unit Wk) : Local W₀ Rc Xi Unit → Ask :=
  askOf K.send (fun w => K.weights w.w₀) fun w => randK14 (K.rand w.rc)

/-- **The prover's shared list finds Omega's sending at its place.** -/
theorem omega_found (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtAll) :
    ((keyProver K).shared.find? fun g => g.place == omegaPlace) =
      some ⟨omegaPlace, [(liftSend
        (fun c : Common W₀ Rc TableKey => ⟨rowsOf K.send.P.S (K.weights c.w₀) (randK14 (K.rand c.rc))⟩)
        (sendingPart (jobOmega ⟨K.send.P, K.send.atPoint⟩)) : Part Empty (Common W₀ Rc TableKey) Unit)]⟩ := by
  have hn : ((keyProver K).shared.map (·.place)).Nodup := by
    rw [AtPublicFiles.KeyFile.keyProver_shared K hA.splits, hA.onU, hA.onOmega]
    decide
  have hm : (⟨omegaPlace, [(liftSend
      (fun c : Common W₀ Rc TableKey => ⟨rowsOf K.send.P.S (K.weights c.w₀) (randK14 (K.rand c.rc))⟩)
      (sendingPart (jobOmega ⟨K.send.P, K.send.atPoint⟩)) : Part Empty (Common W₀ Rc TableKey) Unit)]⟩ :
      Placed Empty (Common W₀ Rc TableKey) Unit) ∈ (keyProver K).shared := by
    have e : (keyProver K).shared =
        AtPublicFiles.KeyFile.sharedChainProverSidesInOrder (K14.proverSidesOfSharedRounds K.lin K.weights)
          (K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++ [K.onU, K.onOmega] := rfl
    rw [e, K14.sendHalves_eq]
    simp only [AtPublicFiles.KeyFile.sharedChainProverSidesInOrder, K14.proverSidesOfSharedRounds, hA.splits]
    simp
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  exact OnBytes.SendSim.Seat.find_of_nodup
    (fun g : Placed Empty (Common W₀ Rc TableKey) Unit => g.place) _ hn _ hm

/-- **The clause trees at every returned run.** -/
theorem trees_own_at_run (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK₀ : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hA : K.AtAll) (f : W₀ → Weights)
    (hidx : K.idx = indexMaskSending Xs) (hw : K.w = batchedRowsSending f Xs N) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hown : K.own = proverSideOfGuardedSending Xs N Pl K.idx K.w K.send id (ownAsk K))
    {P : Prover W₀ Rc KeyInst TableKey Unit Unit Unit} (h1 : P.first = (keyProver K).first)
    (h2 : P.shared = (keyProver K).shared) (h3 : P.second = (keyProver K).second) {w₀ : W₀} {rc : Rc}
    {x : Xi} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hrun : runC (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (st : List (ℕ × ℕ × List UInt64)) :
    TreesAtRun (Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)) piKWFull.nums.first k 2 placeW r.called
      (midAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ) (r.run.beforeAt st) := by
  subst hB
  intro hc m ca hm hca
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts hrun
  obtain ⟨-, tr, -, hRown, hRcom, -, -, -⟩ := ready_ok hR
  have hp := own_sourced hS scope
  have hJ : (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)).p = piKWFull := hp
  have hPW : (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)).p.place = placeW := by
    rw [hJ]
    exact place_KW
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_own_key (Xs := Xs) (N := N) (Pl := Pl) (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)) rfl
    (by rw [hp]; exact place_KW)
  have F : PlaceFacts (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)).p dsKW := by
    rw [hJ]
    exact facts_KWFull
  have hrest : restLen (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)).p.nums.stages ≠ 0 := by
    rw [hJ]
    exact rest_KW_pos
  obtain ⟨σ, hσ, hσb⟩ : ∃ σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Unit Xi,
      Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)).p.place
        (guardRow (testPairs (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)) (simOwnKey Xs N Pl))) [] = some σ ∧ σ.block = b := by
    refine ⟨⟨b, guardRow (testPairs (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)) (simOwnKey Xs N Pl)), fallOf [] (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)).p.place⟩, ?_, rfl⟩
    unfold Side.seated
    show Option.map _ ((keyFileDescription Xs N Pl).second.blocksInOrder.find? fun b => b.place == _) = _
    rw [hf]
    rfl
  have hpl : σ.block.place = placeW := by rw [hσb, hbp, hPW]
  have hg : (P.second.find? fun g => g.place == σ.block.place) =
      some ((proverSideOfProximityTest (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)) : Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit).needsField) := by
    rw [hpl, h3]
    have q := find_own K hown
    rw [own_sourced hS scope, place_KW] at q
    exact q
  have hc₁ : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hpl]
    exact hc
  obtain ⟨pre, t, c, m₁, S, hm₁, -, hin₁, -⟩ := five_at_test₃ hS.named.plan hρ hR (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)) F _ rfl
    (fun s w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh) (simOwnKey Xs N Pl) hJ.symm rfl [] σ
    hσ b hf hbp hr hor hg (by rw [hPW]; exact ties_at_own hK₀ K.idx K.w K.send (ownAsk K)) hrun hc₁
    hrest st
  have hm' := hm₁
  rw [hpl] at hm'
  obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  unfold carriedAt at hca
  obtain ⟨cc, hl, e⟩ := exMap_ok hca
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hS scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  obtain ⟨i1, i2, i3⟩ := idx_plan (Wd := Local W₀ Rc Xi Unit) (Yd := Unit) one
    VerifiableInference.Desc.Key.pieces
    (VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1 0
      (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1 0)) 0
  obtain ⟨Jw, eJ, -, -, -, -, gs, fi, pts, a, hJw⟩ := keyW_written (W₀ := W₀) (Rc := Rc) Xs N f one
  obtain ⟨w1, w2, w3⟩ := w_plan one hJw
  obtain ⟨g1, -, g3⟩ := first_finds K hA.first
  have eQ : parKey Xs Pl = QK := par_sourced hS scope
  have T := own_trees_stand hK₀ scope hS hR hrun σ _ pre t _ S hc₁ st hpl rfl K.idx K.w K.send
    (ownAsk K) (by rw [hidx]; exact i1) (by rw [hidx]; exact i2) (by rw [hidx]; exact i3)
    (by rw [hw, eJ]; exact w1) (by rw [hw, eJ]; exact w2) (by rw [hw, eJ]; exact w3)
    (by rw [hsend]; show (parKey Xs Pl).codes = _; rw [eQ]; exact plan_written.1)
    (by rw [hsend]; show (parKey Xs Pl).S = _; rw [eQ]; exact plan_written.2)
    (by rw [hsend]; show 0 < 4; omega) m₁ hm₁ (by rw [hJ]) _ _ _
    (restPart (jobOwnKey Xs N Pl K.idx K.w K.send (ownAsk K)) : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit) cc
    (by rw [hpl]; exact hl) (by rw [h1]; exact g1) (by rw [h1]; exact g3) _
    (by rw [h2]; exact omega_found K hA)
    (fun w fr fr' hh => by rw [hw]; exact keyW_data_in_front f hS scope w fr fr' hh)
    (by rw [hRcom, hin₁, hRown]; rfl)
  rw [e, hpl] at T
  exact T

end

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.plan_written
#print axioms AtPublicFiles.OfflineRows.omega_found
#print axioms AtPublicFiles.OfflineRows.trees_own_at_run
