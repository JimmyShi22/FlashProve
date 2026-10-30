-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WTiedAtStand.lean: the clause tied of SaysLeft at the filling's job with Omega's member
paid: tied_at_fill, with omega_member_plan, omega_word_at, same_at_W, seats_of_narrow, first_tree_of_laid.

  an_at_filling    the filling's job's third member, at the sending at the plan
  tied_at_stand    WordsTied at that job, at a record behind the block that agrees with the closed shape

Limits, the premises that stay.
- The stand: hc, L, hfirst, hG, hfr, hh, hl₀, hpt, hlen, hNa, hNb, hxc, hhc, hxs, c, hl.
- Public under the head: ht₁, hfb, hco₀, hco₁, hcs, hcq, hpl, hP, n5, hdS, htf, hte, hten, own, hcut.
- hs: the thread's Script is part 5's. hAp: the hash build's sharedTenantsApart.
- NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.WTiedAtFill
import AtFullSide.K12.LettersOmegaCut
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OWordAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K1 (parGF parWF qAt)
open VerifiableInference.Desc.Third (S₃)
open OnBytes.Slice (GE rdE frS)
open OnBytes.Means (layoutOf)
open ProofFile.Honest.K12.AtFile (SameCore narrowW omega_member_plan omega_word_at)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders sharedShape)
open ProofFile.Honest.K12.Light (plainMany WordsTied ManyJob memOfSending askOf)
open Desc.K14.Honest
open ProofFile.Honest.K14
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest.K1 (firstScriptAt)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The filling's job's third member is the sending at the plan.** -/
theorem an_at_filling (hd : HeadAtReturn files A) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill A.Z hd.places hd.firstChain I S O A.G = some M) :
    ∃ (a : Nat) (fs : Option Nat × Option Nat),
      sendPub A.Z = some ⟨qAt A.Z hd.places, a⟩ ∧
      M.mems[2]? = some (memOfSending (jobOmega ⟨qAt A.Z hd.places,
          ((P5J.F0T OnBytes.secondHashFunction A.Z hd.places hd.firstChain).first.blocksInOrder.flatMap
            (·.rounds)).length + a⟩) senderO 0 fs
        (askOf ⟨qAt A.Z hd.places, a⟩ (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => I.weights A.Z w.w₀)
          (fun w => randAt (qAt A.Z hd.places) w.rc)) none) := by
  unfold jobAtFill jobRealW at hM
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨An, hAn, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hM
  have hAn' := hAn
  unfold sendPub at hAn'
  rw [(ProofFile.Honest.K14.readers_at A.Z hd.places hd.head.laid.places).1] at hAn'
  change Option.map _ _ = some An at hAn'
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hAn'
  exact ⟨a, _, hAn, rfl⟩

/-- **WordsTied at the filling's job, at a record behind the block that agrees with the closed shape.** -/
theorem tied_at_stand (hd : HeadAtReturn files A) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill A.Z hd.places hd.firstChain I S O A.G = some M)
    (first : FirstThreadParts A) (hs : first.script = firstScriptAt I S O A hd.firstChain)
    (k : Coins A.B) (v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (fr : Front Unit) (heard : List Fmt.Drawn)
    (hlen : 48290 ≤ heard.length)
    (c : RowCoins [(firstPart M.toRun.toTest :
      Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
      restPart M.toRun.toTest])
    (hl : lendRow A.B (A.B.rowsOf 2) (k.look 2) M.toRun.toTest.p.place
      [(firstPart M.toRun.toTest :
        Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart M.toRun.toTest] 0 = .ok c)
    (hpl : M.toRun.toTest.p.place = placeW)
    (s₀ s : S₃) {b : VerifiableInference.Desc.Third.Border} {y : OnBytes.Oracle} {G' : OnBytes.Group}
    {dot : OnBytes.Row} {Sh : OnBytes.Params.LinShape}
    (L : VerifiableInference.Desc.Third.Laid Sh s₀ s b y G' dot)
    (hfirst : s₀.book.trees.size + 1 = s₀.loc.firstTree) (G : OnBytes.Group)
    (hc : SameCore [4, 197, 198, 199] s.loc.own 0
      (VerifiableInference.Desc.Ground.Sh.coreSh ⟨s.st, s.book, s.roots⟩) narrowW)
    (hG : s.st.groups[s.loc.own]? = some G)
    (ht₁ : 83 ≤ hd.description.t₁) (hAp : ProofFile.Honest.FirstThread.SharedTenantsApart hd)
    (hfb : 0 + roundsTo hd.firstChain.blocksInOrder 356 = 48290)
    (hNa : 0 + roundsTo hd.firstChain.blocksInOrder 2 ≤ heard.length)
    (hNb : 0 + roundsTo hd.firstChain.blocksInOrder 356 ≤ heard.length)
    (hco₀ : parGF.codes = (ToldDesc.p14At A.Z).codes)
    (hco₁ : parWF.codes = (ToldDesc.p14At A.Z).codes) (hcs : s.st.codes = (ToldDesc.p14At A.Z).codes)
    (hfr : ∀ a, fr.heard.take ((K13.wDataAt O.pile A.Z A.G v.x).heardAt a) =
      (heard.take 48290).take ((K13.wDataAt O.pile A.Z A.G v.x).heardAt a))
    {layO : OnBytes.TreeLay}
    (hP : Plan2 (qAt A.Z hd.places) (ProofFile.Honest.K12.Light.sentOf (qAt A.Z hd.places).S) layO)
    (own : Cs (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes)
    (hcut : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes = some own)
    (n5 : (dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.e)
    (hdS : dueAt A.B.shared senderO = (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes)
    (htf : rowOF.2.2.f ≤ (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.f)
    (hte : rowOF.2.2.e ≤ (sendingPart (jobOmega ⟨qAt A.Z hd.places, 0⟩)).takes.e)
    (hl₀ : heard.drop (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length ≠ [])
    (hpt : (Desc.K14.drawn (ProofFile.Honest.K14.firstRv (heard.drop (declsTo hd.description.first.blocksInOrder
              hd.description.first.blocksInOrder.length).length))).length = (qAt A.Z hd.places).par.S.kCol)
    (hh : ∀ a : Nat, sendPub A.Z = some ⟨qAt A.Z hd.places, a⟩ →
      ProofFile.Honest.heardFrom (⟨ProofFile.Honest.K12.AtFile.askR (qAt A.Z hd.places)
                (I.weights A.Z) (randAt (qAt A.Z hd.places)) ⟨v.w₀, v.rc, A.H.key v.x⟩, fr.heard, ()⟩ :
                State ProofFile.Honest.K14.Ask Unit)
        (((P5J.F0T OnBytes.secondHashFunction A.Z hd.places hd.firstChain).first.blocksInOrder.flatMap
          (·.rounds)).length + a) 1 =
      ProofFile.Honest.heardFrom (⟨ProofFile.Honest.K12.AtFile.askR (qAt A.Z hd.places)
                (I.weights A.Z) (randAt (qAt A.Z hd.places)) ⟨v.w₀, v.rc, A.H.key v.x⟩,
              heard.drop (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length,
              ()⟩ : State ProofFile.Honest.K14.Ask Unit) 0 1)
    (hten : hd.sharedNumbers.tenant .oOmega = (((dpZ files).at frS.P.T.a).t₁ + 1, 0))
    (xc : OnBytes.Oracle) (hxc : s.st.oracles[199]? = some xc)
    (hhc : xc.shape = sharedShape A.Z hd.places .oOmega)
    (hxs : xc.shape = (qAt A.Z hd.places).par.S.omega)
    (hcq : s.st.codes = (qAt A.Z hd.places).codes) :
    WordsTied s.st s.loc.own G
      (wordsAtW hd first ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ s k v heard) (layoutOf s.st G)
      (plainMany M v fr (restCoins M.toRun.toTest c.2.1)) := by
  obtain ⟨a, f₂, hAn, hn₂⟩ := an_at_filling hd I S O hM
  have hB := book_at_filling hd.head hA
  have hSh := ProofFile.Honest.K12.Light.sendShapes_head hd.head.toAtMg
  obtain ⟨hQ, hk, hsort, hsh, hl₂, hz₂⟩ := omega_member_plan hd.head.toAtMg hP hSh
    (((P5J.F0T OnBytes.secondHashFunction A.Z hd.places hd.firstChain).first.blocksInOrder.flatMap (·.rounds)).length + a)
  have hft := first_tree_of_laid L hfirst hc
  have hq := omega_row_at_head hd.head hAn
    (((P5J.F0T OnBytes.secondHashFunction A.Z hd.places hd.firstChain).first.blocksInOrder.flatMap (·.rounds)).length + a)
  have same := same_at_W (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) hB _ hq M.toRun.toTest hpl k c hl own
    hcut hdS htf hte
  obtain ⟨-, -, q199⟩ := seats_of_narrow hc ((dpZ files).at frS.P.T.a).t₁
    ((dpZ files).at frS.P.T.a).t₂
  exact tied_at_fill hd I S O hA hM first hs ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ k v fr heard
    hlen c hl hpl s G hc hG hft ht₁ hAp hfb hNa hNb hco₀ hco₁ hcs hfr
    ⟨qAt A.Z hd.places, a⟩ _ f₂ _ hn₂ hQ hk _ hsort _ _ rfl same
    (by rw [hft, hten]; exact q199) xc hxc hhc (hxs.trans hsh.symm) (hxs.trans hsh.symm).symm hcq
    hl₂ hz₂
    (fun pt i => omega_word_at hd ⟨I.weights A.Z, randAt (qAt A.Z hd.places)⟩ k v heard hP hSh own hcut
      n5 hl₀ hpt _ fr.heard (hh a hAn) pt i)

end AtFullSide.K12

#print axioms AtFullSide.K12.tied_at_stand
#print axioms AtFullSide.K12.an_at_filling
