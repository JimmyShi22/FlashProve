-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WTiedAtFill.lean: the clause tied of SaysLeft (K12/AtFile/WSays.lean) at the last chain's
test, at the job that the filling returns, at the words of which the last thread's item "rows"
speaks: the members' tables are the senders'.

  tied_of_parts  WordsTied at a job of the three members, from the senders' parts, general in the jobs
  tied_at_fill   WordsTied at the filling's job, at a record that agrees with the closed shape

By what. words_tied_three, sent_at_W, seats_of_narrow, shape_of_narrow, members_of_narrow,
first_member_at_filling, w_member_at_filling, tie_k1_first, held_cut_I, held_cut_W, member_coins_at_W.

Limits, the premises that stay.
- hc: the record's shape, at the stand: sameCore_at_seat.
- hft: the last chain's first tree is 84: first_tree_of_laid (WSeatsNarrow.lean), from what the block laid
  and the count in front of it.
- hO, same, hs₂, hl₂, hz₂, hJs, hsc, hxc: Omega's member: its sending's tables, coins and shape.
- ht₁, hco₀, hco₁, hcs, hfb, hNa, hNb: public numbers under the head, and rounds heard at the stand.
- hAp: the hash build's sharedTenantsApart has it under the head (K14/WordsAtLastWitness.lean).
- hfr: what the job's data read of the test's front is what was heard in front of the sender.
- NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.LettersAtHead
import AtFullSide.K12.WNumbersAtHead
import AtFullSide.K12.WMemberCoins
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsTiedAtW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsTiedJobW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K1 (parGF parWF)
open VerifiableInference.Desc.Third (S₃)
open OnBytes.Slice (GE rdE frS)
open OnBytes.Means (layoutOf)
open ProofFile.Honest.K12.AtFile (SameCore narrowW)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders lastWitness sharedShape)
open ProofFile.Honest.K12.Light (plainMany WordsTied SameCut vecAt ManyJob memOfSending)
open VerifierAndGoals.AtTheName (dpZ)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (firstScriptAt tie_k1_first jobTwoAt jobWAt k1MembersW k1Members)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **WordsTied at a job of the three members, from the senders' parts.** General in the two K1 jobs. -/
theorem tied_of_parts (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ IndexCommitterCoins) (hAp : ProofFile.Honest.FirstThread.SharedTenantsApart hd)
    (ht₁ : 83 ≤ hd.description.t₁) (k : Coins A.B) (v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (fr : Front Unit) (heard : List Fmt.Drawn)
    {Na Nb : Nat} (hNa : Na ≤ heard.length) (hNb : Nb ≤ heard.length)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) (C : TestCoins)
    (s : S₃) (G : OnBytes.Group)
    (hc : SameCore [4, 197, 198, 199] s.loc.own 0
      (VerifiableInference.Desc.Ground.Sh.coreSh ⟨s.st, s.book, s.roots⟩) narrowW)
    (hG : s.st.groups[s.loc.own]? = some G) (hft : s.loc.firstTree = 84)
    (hcs : s.st.codes = (ToldDesc.p14At A.Z).codes)
    (J₀ J₁ : ProofFile.Honest.K1.SendJob (K1.PlaceIn ProofFile.Inst) Unit)
    (wa : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst)
    (eI : J₀.P = parGF) (eW : J₁.P = parWF)
    (hco₀ : parGF.codes = (ToldDesc.p14At A.Z).codes)
    (hco₁ : parWF.codes = (ToldDesc.p14At A.Z).codes)
    (fs₀ fs₁ : Option Nat × Option Nat)
    (e₀ : M.mems[0]? = some (memK1 J₀ wa senderI (J₀.P.sent.size - 1) fs₀))
    (e₁ : M.mems[1]? = some (memK1 J₁ wa senderW 0 fs₁))
    (s₂ : ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 2 parGF (parGF.sent.size - 1) = (1, 0))
    (s₃ : ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 356 parWF 0 = (82, 0))
    (ma : ∀ n, n < J₀.P.sent.size → ProofFile.Honest.FirstThread.OwnMsgs first.script (fun _ => True) Na
      (P5J.At.arr A.Z (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 2 J₀.P n).1
        (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 2 J₀.P n).2) Na
      (ProofFile.Honest.K1.msgTxt 0 wa J₀ () n))
    (pa : ∀ n, n < J₀.P.sent.size → ProofFile.Honest.FirstThread.OwnPads first.script (fun _ => True)
      (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 2 J₀.P n).1
      (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 2 J₀.P n).2
      (fun k _ => ProofFile.Honest.K1.padTxt 0 J₀ n k))
    (mb : ∀ n, n < J₁.P.sent.size → ProofFile.Honest.FirstThread.OwnMsgs first.script (fun _ => True) Nb
      (P5J.At.arr A.Z (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 356 J₁.P n).1
        (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 356 J₁.P n).2) Nb
      (ProofFile.Honest.K1.msgTxt 0 wa J₁ () n))
    (pb : ∀ n, n < J₁.P.sent.size → ProofFile.Honest.FirstThread.OwnPads first.script (fun _ => True)
      (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 356 J₁.P n).1
      (ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 356 J₁.P n).2
      (fun k _ => ProofFile.Honest.K1.padTxt 0 J₁ n k))
    (c₀ : Cs (K1.dueR J₀.P J₀.ride))
    (hc₀ : K1.lentCut k 0 ⟨J₀.P.place, 0⟩ (K1.dueR J₀.P J₀.ride) = some c₀)
    (f₀ : ∀ i, i < (K1.dueMsg J₀.P.codes (shapeAt J₀.P (J₀.P.sent.size - 1))
        (J₀.ride (J₀.P.sent.size - 1))).f →
      K1.cf c₀ ((K1.startR J₀.P J₀.ride (J₀.P.sent.size - 1)).f + i) = (C.mem 0).f i)
    (g₀ : ∀ i, i < (K1.dueMsg J₀.P.codes (shapeAt J₀.P (J₀.P.sent.size - 1))
        (J₀.ride (J₀.P.sent.size - 1))).e →
      K1.ce c₀ ((K1.startR J₀.P J₀.ride (J₀.P.sent.size - 1)).e + i) = (C.mem 0).e i)
    (c₁ : Cs (K1.dueR J₁.P J₁.ride))
    (hc₁ : K1.lentCut k 0 ⟨J₁.P.place, 0⟩ (K1.dueR J₁.P J₁.ride) = some c₁)
    (hR₁ : ProofFile.Honest.K1.rowsLaid J₁ () c₁ (wa v) (heard.take Nb) 0 =
      K1.rowsR J₁.P J₁.ride (J₁.data (wa v) fr) (csAt _ (K1.startR J₁.P J₁.ride 0) (C.mem 1)) 0)
    (An : ProofFile.Honest.K14.SendPub) (n₁ : Nat) (f₂ : Option Nat × Option Nat)
    (ask : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → ProofFile.Honest.K14.Ask)
    (hn₂ : M.mems[2]? = some (memOfSending (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) senderO 0 f₂ ask none))
    (hQ : ProofFile.Honest.K14.sendingsFit An.P = true)
    (hk : 0 < (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.sent.size) (high : Bool)
    (hsort : (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).sort 0 = .plain high)
    (t : State ProofFile.Honest.K14.Ask Unit) (cs : Array OnBytes.E)
    (hv : vecAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0 ask none v fr =
      (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).data t 0)
    (same : SameCut (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0 cs (C.mem 2))
    (hsc : VerifiableInference.Desc.Sound.seatBy (VerifiableInference.Desc.Sound.noLast
      ((dpZ files).at frS.P.T.a).t₁ ((dpZ files).at frS.P.T.a).t₂ s.loc.firstTree) s.book 199 =
        some ((hd.sharedNumbers.tenant .oOmega).1, (hd.sharedNumbers.tenant .oOmega).2))
    (xc : OnBytes.Oracle) (hxc : s.st.oracles[199]? = some xc)
    (hhc : xc.shape = sharedShape A.Z hd.places .oOmega)
    (hhs : xc.shape = ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0)
    (hhs' : ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.sent.getD 0 default).shape = xc.shape)
    (hcq : s.st.codes = (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes)
    (hl₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).mainRows →
      ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.base.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).code default).ell =
      2 ^ ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.base.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).code default).logEll)
    (hz₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).maskRows →
      ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.mask.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).maskCode default).ell =
      2 ^ ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.mask.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).maskCode
        default).logEll)
    (hO : ∀ pt i, omegaWord hd reads k v heard pt i =
      rdE.val (ProofFile.Honest.K14.wordsOf (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.sent
        ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).rows t cs) 0 pt i)) :
    WordsTied s.st s.loc.own G (wordsAtW hd first reads s k v heard) (layoutOf s.st G)
      (plainMany M v fr C) := by
  have hmem : G.members = #[4, 197, 199] := members_of_narrow hc hG
  obtain ⟨q4, q197, q199⟩ := seats_of_narrow hc ((dpZ files).at frS.P.T.a).t₁
    ((dpZ files).at frS.P.T.a).t₂
  obtain ⟨y4, y197, -⟩ := narrow_shapes
  have h4 := (shape_of_narrow hc 4 (by decide)).trans y4
  have h197 := (shape_of_narrow hc 197 (by decide)).trans y197
  obtain ⟨xa, hxa, hha⟩ := Option.map_eq_some_iff.1 h4
  obtain ⟨xb, hxb, hhb⟩ := Option.map_eq_some_iff.1 h197
  have hn0 : J₀.P.sent.size - 1 < J₀.P.sent.size := by
    rw [eI]
    decide
  have hn1 : 0 < J₁.P.sent.size := by
    rw [eW]
    decide
  have ea : ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 2 J₀.P (J₀.P.sent.size - 1) = (1, 0) := by
    rw [eI]
    exact s₂
  have eb : ProofFile.Honest.K1.seatAtMember hd.firstChain.blocksInOrder 356 J₁.P 0 = (82, 0) := by
    rw [eW]
    exact s₃
  have ma' := ma _ hn0
  have pa' := pa _ hn0
  have mb' := mb 0 hn1
  have pb' := pb 0 hn1
  rw [ea] at ma' pa'
  rw [eb] at mb' pb'
  have hmain : (shapeAt J₀.P (J₀.P.sent.size - 1)).mainRows = 0 := by
    rw [eI]
    exact first_last_no_main
  have E := sent_at_W hd first reads hAp.1 (fun _ => True) Na Nb k v trivial heard hNa hNb s
    wa J₀ () Na (J₀.P.sent.size - 1) 1 0 (far_of_apart hd hAp 1 0 (by omega)) ma' pa' c₀ hc₀ 4 xa
    (by rw [hft]; exact q4) hxa (by rw [eI]; exact hha) (by rw [eI]; exact hco₀)
    wa J₁ () Nb 0 82 0 (far_of_apart hd hAp 82 0 (by omega)) mb' pb' c₁ hc₁ 197 xb
    (by rw [hft]; exact q197) hxb (by rw [eW]; exact hhb) (by rw [eW]; exact hco₁)
    (K1.rowsR J₀.P J₀.ride (J₀.data (wa v) fr)
      (csAt _ (K1.startR J₀.P J₀.ride (J₀.P.sent.size - 1)) (C.mem 0)) (J₀.P.sent.size - 1))
    (K1.rowsR J₁.P J₁.ride (J₁.data (wa v) fr) (csAt _ (K1.startR J₁.P J₁.ride 0) (C.mem 1)) 0)
    (by
      unfold ProofFile.Honest.K1.rowsLaid
      exact (rowsR_no_main _ _ _ (J₀.data (wa v) fr) _ _ hmain).trans
        (rowsR_csAt _ _ (J₀.data (wa v) fr) _ hn0 _ c₀ f₀ g₀).symm)
    hR₁ 199 xc (by rw [hft] at hsc ⊢; exact hsc) hxc hhc (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) t cs 0 hhs' hO
  obtain ⟨d₀, d₁, d₂⟩ := find_three (layoutOf s.st G) hmem
  exact words_tied_three M v fr C J₀ J₁ wa wa senderI senderW senderO _ 0 fs₀ fs₁ f₂ e₀ e₁ An.P hQ
    (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) (Or.inr ⟨rfl, rfl⟩) 0 hk high hsort ask t hv cs hn₂ same
    s.st s.loc.own G (layoutOf s.st G) 4 197 199 hmem d₀ d₁ d₂ (by rw [eI]; exact h4)
    (by rw [eW]; exact h197) (by rw [hxc]; exact congrArg some hhs) (by rw [eI]; exact hcs.trans hco₀.symm)
    (by rw [eW]; exact hcs.trans hco₁.symm) hcq (by rw [eI]; exact ells_written.2.1)
    (by rw [eI]; exact ells_written.1) (by rw [eW]; exact ells_written.2.2.1)
    (by rw [eW]; exact ells_written.2.2.2) hl₂ hz₂ _ E

/-- **WordsTied at the filling's job, at a record that agrees with the closed shape.** -/
theorem tied_at_fill (hd : HeadAtReturn files A) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill A.Z hd.places hd.firstChain I S O A.G = some M)
    (first : FirstThreadParts A) (hs : first.script = firstScriptAt I S O A hd.firstChain)
    (reads : IndexReaders W₀ IndexCommitterCoins) (k : Coins A.B) (v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (fr : Front Unit) (heard : List Fmt.Drawn) (hlen : 48290 ≤ heard.length)
    (c : RowCoins [(firstPart M.toRun.toTest :
      Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
      restPart M.toRun.toTest])
    (hl : lendRow A.B (A.B.rowsOf 2) (k.look 2) M.toRun.toTest.p.place
      [(firstPart M.toRun.toTest :
        Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart M.toRun.toTest] 0 = .ok c)
    (hpl : M.toRun.toTest.p.place = placeW)
    (s : S₃) (G : OnBytes.Group)
    (hc : SameCore [4, 197, 198, 199] s.loc.own 0
      (VerifiableInference.Desc.Ground.Sh.coreSh ⟨s.st, s.book, s.roots⟩) narrowW)
    (hG : s.st.groups[s.loc.own]? = some G) (hft : s.loc.firstTree = 84)
    (ht₁ : 83 ≤ hd.description.t₁) (hAp : ProofFile.Honest.FirstThread.SharedTenantsApart hd)
    (hfb : 0 + roundsTo hd.firstChain.blocksInOrder 356 = 48290)
    (hNa : 0 + roundsTo hd.firstChain.blocksInOrder 2 ≤ heard.length)
    (hNb : 0 + roundsTo hd.firstChain.blocksInOrder 356 ≤ heard.length)
    (hco₀ : parGF.codes = (ToldDesc.p14At A.Z).codes)
    (hco₁ : parWF.codes = (ToldDesc.p14At A.Z).codes) (hcs : s.st.codes = (ToldDesc.p14At A.Z).codes)
    (hfr : ∀ a, fr.heard.take ((K13.wDataAt O.pile A.Z A.G v.x).heardAt a) =
      (heard.take 48290).take ((K13.wDataAt O.pile A.Z A.G v.x).heardAt a))
    (An : ProofFile.Honest.K14.SendPub) (n₁ : Nat) (f₂ : Option Nat × Option Nat)
    (ask : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → ProofFile.Honest.K14.Ask)
    (hn₂ : M.mems[2]? = some (memOfSending (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) senderO 0 f₂ ask none))
    (hQ : ProofFile.Honest.K14.sendingsFit An.P = true)
    (hk : 0 < (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.sent.size) (high : Bool)
    (hsort : (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).sort 0 = .plain high)
    (t : State ProofFile.Honest.K14.Ask Unit) (cs : Array OnBytes.E)
    (hv : vecAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0 ask none v fr =
      (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).data t 0)
    (same : SameCut (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0 cs ((restCoins M.toRun.toTest c.2.1).mem 2))
    (hsc : VerifiableInference.Desc.Sound.seatBy (VerifiableInference.Desc.Sound.noLast
      ((dpZ files).at frS.P.T.a).t₁ ((dpZ files).at frS.P.T.a).t₂ s.loc.firstTree) s.book 199 =
        some ((hd.sharedNumbers.tenant .oOmega).1, (hd.sharedNumbers.tenant .oOmega).2))
    (xc : OnBytes.Oracle) (hxc : s.st.oracles[199]? = some xc)
    (hhc : xc.shape = sharedShape A.Z hd.places .oOmega)
    (hhs : xc.shape = ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0)
    (hhs' : ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.sent.getD 0 default).shape = xc.shape)
    (hcq : s.st.codes = (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes)
    (hl₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).mainRows →
      ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.base.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).code default).ell =
      2 ^ ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.base.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).code default).logEll)
    (hz₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).maskRows →
      ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.mask.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).maskCode default).ell =
      2 ^ ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.codes.mask.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩) 0).maskCode
        default).logEll)
    (hO : ∀ pt i, omegaWord hd reads k v heard pt i =
      rdE.val (ProofFile.Honest.K14.wordsOf (ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).Q.sent
        ((ProofFile.Honest.K14.jobOmega ⟨An.P, n₁⟩).rows t cs) 0 pt i)) :
    WordsTied s.st s.loc.own G (wordsAtW hd first reads s k v heard) (layoutOf s.st G)
      (plainMany M v fr (restCoins M.toRun.toTest c.2.1)) := by
  obtain ⟨Bs, base, Op⟩ := hd.head.laid.opened
  have hB := book_at_filling hd.head hA
  obtain ⟨fs₀, e₀, -⟩ := first_member_at_filling hd.head I S O hA hM
  obtain ⟨fs₁, e₁, -⟩ := w_member_at_filling hd.head I S O hA hM
  have eG := ground_at_head hd.head.laid Op hA
  have eI : (firstOfLot (X := Unit) OnBytes.secondHashFunction S A.Z A.G).P = parGF := by
    show VerifiableInference.Desc.K1.firstPar A.G.first (VerifiableInference.Desc.K1.gpOf A.Z) = _
    rw [eG]
    exact VerifiableInference.Desc.K1.eG_atAll hd.head Op (VerifiableInference.Desc.K1.pin1_atAll hd.head)
  have eW : (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
      VerifiableInference.Desc.K13.Law.wMsgFull).P = parWF := ProofFile.Honest.K1.parW_written hd.head Op
  have rI : (firstOfLot (X := Unit) OnBytes.secondHashFunction S A.Z A.G).ride = rideGF := by
    show K1.rideOf (K1.firstFold A.G.first) = _
    rw [eG]
    exact ProofFile.Honest.K1.ride_two_head hd.head Op
  have rW : (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
      VerifiableInference.Desc.K13.Law.wMsgFull).ride = rideWF := ProofFile.Honest.K1.ride_w_head hd.head Op
  obtain ⟨mI, mW⟩ := member_coins_at_W (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) hB M.toRun.toTest hpl k c hl
  obtain ⟨s₂, s₃₅₆⟩ := seats_at_head hd.head.toAtMg Op
  have t₂ := tie_k1_first (I := I) (S := S) (Op := O) hd.head hA (fun _ => True)
    (y := (2, jobTwoAt S A.Z A.G))
    (ProofFile.Honest.K1.mem_k1MembersW.2 (Or.inl (ProofFile.Honest.K1.mem_k1Members.2 (Or.inl rfl))))
  have t₃ := tie_k1_first (I := I) (S := S) (Op := O) hd.head hA (fun _ => True)
    (y := (356, jobWAt O A.Z A.G)) (ProofFile.Honest.K1.mem_k1MembersW.2 (Or.inr rfl))
  rw [← hs] at t₂ t₃
  obtain ⟨c₀, hc₀, f₀, g₀⟩ := held_cut_I hB (firstOfLot (X := Unit) OnBytes.secondHashFunction S A.Z A.G) eI rI k _
    (fun h => mI h)
  obtain ⟨c₁, hc₁, f₁, g₁⟩ := held_cut_W hB (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
    VerifiableInference.Desc.K13.Law.wMsgFull) eW rW k _ (fun h => mW h)
  have hn1 : 0 < (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
      VerifiableInference.Desc.K13.Law.wMsgFull).P.sent.size := by
    rw [eW]
    decide
  have hR₁ : ProofFile.Honest.K1.rowsLaid (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
            VerifiableInference.Desc.K13.Law.wMsgFull) () c₁ (inOf (lettersW I A.Z) v)
      (heard.take (0 + roundsTo hd.firstChain.blocksInOrder 356)) 0 =
      K1.rowsR (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
          VerifiableInference.Desc.K13.Law.wMsgFull).P
        (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G VerifiableInference.Desc.K13.Law.wMsgFull).ride
        ((wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G VerifiableInference.Desc.K13.Law.wMsgFull).data
          (inOf (lettersW I A.Z) v) fr)
        (csAt _ (K1.startR (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
          VerifiableInference.Desc.K13.Law.wMsgFull).P (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
          VerifiableInference.Desc.K13.Law.wMsgFull).ride 0) ((restCoins M.toRun.toTest c.2.1).mem 1))
        0 := by
    rw [hfb]
    exact (wMember_rows _ _ _ _ _ (inOf (lettersW I A.Z) v) fr
      { heard := heard.take 48290, own := (), seen := .bare [] } hfr 0 hn1 _ c₁ f₁ g₁).symm
  exact tied_of_parts hd first reads hAp ht₁ k v fr heard hNa hNb M _ s G hc hG hft hcs
    (firstOfLot (X := Unit) OnBytes.secondHashFunction S A.Z A.G) (wJobOf (X := Unit) OnBytes.secondHashFunction O A.Z A.G
                  VerifiableInference.Desc.K13.Law.wMsgFull)
    (inOf (lettersW I A.Z)) eI eW hco₀ hco₁ fs₀ fs₁ e₀ e₁ s₂ s₃₅₆ t₂.1 t₂.2 t₃.1 t₃.2 c₀ hc₀ f₀ g₀ c₁ hc₁ hR₁
    An n₁ f₂ ask hn₂ hQ hk high hsort t cs hv same hsc xc hxc hhc hhs hhs' hcq
    hl₂ hz₂ hO

end AtFullSide.K12

#print axioms AtFullSide.K12.tied_at_fill
