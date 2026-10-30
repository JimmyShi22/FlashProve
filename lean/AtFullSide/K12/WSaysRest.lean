-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WSaysRest.lean: the clause saysAt of StandRest (K12/AtFile/WTable.lean) at ProofFile's last
thread and the filling's job, from a stand at number 2: the words are wordsAtW at what the run has heard.

  saysAt_rest   ∃ ws, SaysLeft at every stand and every row of coins

By what. saysLeft_at_stand, tied_at_stand, core_at_stand, first_tree_of_laid (through tied_at_stand),
ends_at_lastThread, booked_of_behind, behindOk_of_two, point_of_fit, rounds_at_head, codes_at_head.

Limits, the premises that stay.
- hF, hEnter: the field, and the way in: enters_at_W has the second from LetterAtW and hF.
- hsam: the sample rows: samples_at_W_at_run, samples_at_W_from_threads.
- hs: the thread's Script is part 5's.
- Public under the head: hAp, hpl, hP, hcov, n5, hdS, htf, hte, ht₁, hten, hpoint, hx199, hso, ha.
- NOT IN FRONT OF A LAW OVER COINS: it stands behind ThrS.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.WTiedAtStand
import AtFullSide.K12.WSaysAtStand
import AtFullSide.K12.WPublicAtHead
import AtFullSide.K12.LettersHone
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WCoreAtStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointJoined
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointSamplesAtShape
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K1 (parGF parWF qAt)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open OnBytes.Slice (rdE frS)
open OnBytes.Means (sampleItem)
open ProofFile.Honest.K12.AtFile (SameCore narrowW SaysLeft FieldAtW core_at_stand point_of_fit)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW ends_at_lastThread booked_of_behind)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread
  sharedShape)
open ProofFile.Honest.K12.Light (ManyJob)
open Desc.K14.Honest
open ProofFile.Honest.K14
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest.K1 (firstScriptAt)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The clause saysAt of StandRest at ProofFile's last thread, at the filling's job.** -/
theorem saysAt_rest (hd : HeadAtReturn files A) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill A.Z hd.places hd.firstChain I S O A.G = some M)
    (first : FirstThreadParts A) (hs : first.script = firstScriptAt I S O A hd.firstChain)
    (parts : LastThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hF : FieldAtW (P5J.F0T OnBytes.secondHashFunction A.Z hd.places hd.firstChain)
      (lastThread hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ parts w) Said 2)
    (hEnter : ∀ k st m E, ThrS (lastThread hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ parts w)
      Said 2 k st m E → enterOwn st = .ok (M.rec₀ m.st.input (frontOf m)))
    (hsam : ∀ k st m E, ThrS (lastThread hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ parts w)
      Said 2 k st m E → ∀ G, st.st.groups[st.loc.own]? = some G →
        sampleItem rdE st.st G.members.toList
          (wordsAtW hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ st k m.st.input
            (m.st.heard ++ [])))
    (hAp : ProofFile.Honest.FirstThread.SharedTenantsApart hd)
    (hpl : M.toRun.toTest.p.place = placeW)
    {layO : OnBytes.TreeLay}
    (hP : Plan2 (qAt A.Z hd.places) (ProofFile.Honest.K12.Light.sentOf (qAt A.Z hd.places).S) layO)
    (hcov : ∀ k : Coins A.B, ∃ own, (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes = some own)
    (n5 : (dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.e)
    (hdS : dueAt A.B.shared senderO = (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes)
    (htf : rowOF.2.2.f ≤ (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.f)
    (hte : rowOF.2.2.e ≤ (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.e)
    (ht₁ : 83 ≤ hd.description.t₁)
    (hten : hd.sharedNumbers.tenant .oOmega = (((dpZ files).at frS.P.T.a).t₁ + 1, 0))
    (hpoint : ((declsTo hd.description.shared.blocksInOrder hd.description.shared.blocksInOrder.length).head?).map
      (·.entry.drawE) = some (qAt A.Z hd.places).par.S.kCol)
    (hx199 : (narrowW.st.oracles[199]?).map (·.shape) = some (qAt A.Z hd.places).par.S.omega)
    (hso : sharedShape A.Z hd.places .oOmega = (qAt A.Z hd.places).par.S.omega)
    (ha : ∀ a, sendPub A.Z = some ⟨qAt A.Z hd.places, a⟩ → a = 0) :
    ∀ k st m E (c : RowCoins [(firstPart M.toRun.toTest :
        Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart M.toRun.toTest]),
      ThrS (lastThread hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ parts w) Said 2 k st m E →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) M.toRun.toTest.p.place
        [(firstPart M.toRun.toTest :
          Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
          restPart M.toRun.toTest] 0 = .ok c →
      ∃ ws, SaysLeft M m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1) st ws := by
  intro k st m E c u hl
  have hE := hEnter k st m E u
  have hc : SameCore [4, 197, 198, 199] st.loc.own 0
      (VerifiableInference.Desc.Ground.Sh.coreSh ⟨st.st, st.book, st.roots⟩) narrowW :=
    core_at_stand A.Z hd.places hd.firstChain A.H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w hd.head Said M hF u hE
  obtain ⟨f, e, -, -, hk⟩ := ends_at_lastThread hd first _ parts w u.1
  obtain ⟨⟨s₀, B⟩, -⟩ := VerifiableInference.Desc.Last.behindOk_of_two hk
  obtain ⟨-, hBk, -⟩ := booked_of_behind B
  obtain ⟨b, y, G', dot, L⟩ := B.laid
  obtain ⟨own, hown⟩ := hcov k
  have hfit : drawsFit ((declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length ++
      declsTo hd.description.shared.blocksInOrder hd.description.shared.blocksInOrder.length) ++
      declsTo (lastThread hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ parts w).bs 2)
      m.st.heard = true := u.1.2.1
  have hle := congrArg List.length (AtFullSide.K12.drawsFit_elems _ _ hfit)
  simp only [List.length_map, List.length_append] at hle
  have cut := (ProofFile.Honest.drawsFit_cut (declsTo hd.description.first.blocksInOrder
          hd.description.first.blocksInOrder.length).length _ _ hfit).2
  rw [List.append_assoc, List.drop_left] at cut
  have hhd : ((declsTo hd.description.shared.blocksInOrder hd.description.shared.blocksInOrder.length ++
      declsTo (lastThread hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ parts w).bs 2).head?).map
      (·.entry.drawE) = some (qAt A.Z hd.places).par.S.kCol := by
    cases hds : declsTo hd.description.shared.blocksInOrder hd.description.shared.blocksInOrder.length with
    | nil =>
      rw [hds] at hpoint
      cases hpoint
    | cons d tl =>
      rw [hds] at hpoint
      exact hpoint
  obtain ⟨hne, hlp⟩ := point_of_fit _ _ hhd _ cut
  have hr := rounds_at_head hd.head
  have hcd := codes_at_head hd.head.toAtMg
  have hN₁ : 48290 ≤ (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length := by
    have e := ProofFile.Honest.roundsTo_mono hd.firstChain.blocksInOrder 356 hd.firstChain.blocksInOrder.length
      (ProofFile.Honest.K13.k13_len356 hd.head)
    rw [hr.2] at e
    exact e
  have hlen : 48290 ≤ (m.st.heard ++ []).length := by
    rw [List.append_nil]
    omega
  have hcodes : st.st.codes = H2K.Member.codesFull := hc.codes.symm.trans codes_written.2.2
  have h199 := (shape_of_narrow (T := ⟨st.st, st.book, st.roots⟩) hc 199 (by decide)).trans hx199
  obtain ⟨xc, hxc, hxs⟩ := Option.map_eq_some_iff.1 h199
  refine ⟨_, saysLeft_at_stand hd first _ parts w M _ (frontOf m) u.1 [] hE (hsam k st m E u) ?_⟩
  intro G hG
  refine tied_at_stand hd I S O hA hM first hs k m.st.input (frontOf m) (m.st.heard ++ []) hlen c hl hpl
    s₀ st L hBk.first G hc hG ht₁ hAp (by rw [Nat.zero_add]; exact hr.2)
    (by rw [Nat.zero_add]; exact Nat.le_trans hr.1 hlen)
    (by rw [Nat.zero_add, hr.2]; exact hlen)
    (codes_written.1.trans hcd.1.symm) (codes_written.2.1.trans hcd.1.symm) (hcodes.trans hcd.1.symm)
    ?_ hP own hown n5 hdS htf hte ?_ ?_ ?_ hten xc hxc (hxs.trans hso.symm) hxs (hcodes.trans hcd.2.symm)
  · intro a
    show m.st.heard.take (K13.wHeard A.Z) = ((m.st.heard ++ []).take 48290).take (K13.wHeard A.Z)
    rw [AtFullSide.K13.k13_wHeard_at_head hd.head, List.append_nil, List.take_take, Nat.min_self]
  · rw [List.append_nil]
    exact hne
  · rw [List.append_nil]
    exact hlp
  · intro a hA'
    obtain rfl := ha a hA' 
    show ((m.st.heard.drop _).take 1) = (((m.st.heard ++ []).drop _).drop 0).take 1
    rw [List.append_nil, List.drop_zero, Nat.add_zero]
    have ed : declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length =
        hd.description.first.blocksInOrder.flatMap (·.rounds) := by
      unfold declsTo
      rw [List.take_length]
    rw [ed]

end AtFullSide.K12

#print axioms AtFullSide.K12.saysAt_rest
