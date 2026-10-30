-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshSwitch.lean: the closing of a segment (K10): the pairing of the field fresh of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean) at a segment whose fresh mask a code switch has sent (every segment but the first):
the five clauses of `fresh_of_sender` (Pay/XchFreshJoin.lean), paid from the switch's own laws as far as these reach.

  `mask_code_of_base`   under `CloseBase`: the fresh mask's message has 2 ^ h mask rows of the frame's mask code
  `sent_fresh_coins`    `sent_fresh_mask` (Pay/XchFreshSent.lean) with its coins said by the reader that refuses beyond the count
  **`fresh_of_switch`**   the pairing. Its premises:
      hm, hp    the two ties on the script at the switch's last message: its text off the pad, its pad's text
      hH, hV    the switch is handed its coins off the same look-up as the closing's part, and its rows are laid
      hcodes, hshape, hq, hnum, hfv   public: the statement's codes are the switch's; the mask's message has the shape of the
                switch's last message, the seat (j, t) and the number num in the witness; the switch's count of the next fold's
                row variables is the closing's
      hbook     on the book: an entry by which the closing's part spends is owned by the switch's part and starts where the
                last message's mask coins start among the switch's own

Limits. The premises are shown here of no script, book or run. No head and no thread is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshJoin
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshSent
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff
import Johnson.Desc.ProofFile.Honest.K2.Law.SenderOwn
import Johnson.Desc.ProofFile.Honest.K12.Sim.SenderInFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE ceilLog2_two_pow)
open Cb (HIdx sVars)
open Johnson.Prover.Link (Pairs)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.K2.Honest (zeroG)
open VerifiableInference.Desc.Sound (MsgT wordsFirst seatBy noFirst)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open ProofFile.Honest.K2 (SwitchPlace Closing Stretch freshTable fromE rowsAll dueBefore sendingDue switchSent switchFresh NoWord
  handed switchRowsLaid switchMsgOff switchPadTxt)
open ProofFile.Honest.K2.Law (SwitchCoins)
open ProofFile.Honest.K10.LeftIs (stageB freshB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-- Under `CloseBase`: the fresh mask's message has 2 ^ h mask rows of the frame's mask code. -/
theorem mask_code_of_base {P : Par} {r : Rec} {D : BaseData} (Hb : CloseBase P r D) :
    ∃ y, r.st.oracles[D.m]? = some y ∧ y.shape.maskRows = 2 ^ (stageB D r).h ∧
      y.shape.maskCode = r.frame.shape.maskCode := by
  obtain ⟨o, ho, -, hm, hc, -⟩ := (Own.foldMaskFits_iff _ _ _).1 Hb.maskfits
  have e : ((D.S1 r).oracles[D.m]?).map (·.shape) = (r.st.oracles[D.m]?).map (·.shape) :=
    OnBytes.Slice.closeLedgers_shape D.G.members.toList r.st D.m
  rw [ho] at e
  have e' : (r.st.oracles[D.m]?).map (·.shape) = some o.shape := e.symm
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 e'
  refine ⟨y, hy, ?_, ?_⟩
  · rw [ey]
    exact hm
  · rw [ey]
    exact hc

/-- What a sending lays at the message that is a fold's fresh mask; its coins by the reader that refuses beyond the count. -/
theorem sent_fresh_coins {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Johnson.Prover.Send.Rows}
    (h : rowsAll freshTable codes sent fresh data c = .ok V) {n fv : Nat} (hn : n < sent.size)
    (hf : K2.foldAt fresh n = some fv) :
    ∃ c₀ : Nat → GE,
      (∀ t, t < 2 * fv + 1 →
        c.eAt ((dueBefore codes sent fresh n).e + (fromE codes (sent.getD n default).shape + t)) = .ok (c₀ t)) ∧
      ∀ r i, r < (sent.getD n default).shape.maskRows →
        i < (codes.mask.getD (sent.getD n default).shape.maskCode default).ell →
        (V n).mask r i =
          (⟨fv, OnBytes.ceilLog2 (sent.getD n default).shape.maskRows⟩ : K1.Ride).lay c₀ r i := by
  obtain ⟨c', hc', hm⟩ := K2.rowsAll_at h hn
  obtain ⟨cM, hM, hR⟩ := fresh_mask_at hf hm
  exact ⟨(cM.getD · zeroG), fun t ht => K2.Reads.cut_eAt hc' (hM t ht), hR⟩

variable {V' W₀ Rc Xi Tr X Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **The field fresh's pairing at a segment whose fresh mask a code switch has sent.** -/
theorem fresh_of_switch {P : Par} {D : BaseData} {s : First.S} (Hb : CloseBase P (K9.recOf s) D)
    (arr : Nat → Nat → Nat) (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (Dt : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (fx num j t : Nat)
    (hm : OwnMsgs Q Vd N num fx (switchMsgOff 0 Dt readers closing p ((switchSent p.sizes p.others).size - 1)))
    (hp : OwnPads Q Vd j t (fun k _ => switchPadTxt 0 p ((switchSent p.sizes p.others).size - 1) k))
    (hw : NoWord (switchSent p.sizes p.others)) (hpos : 0 < (switchSent p.sizes p.others).size)
    (k : Coins Bk) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed 0 p k = some c) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn)
    (hN : N ≤ hd.length) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid Dt readers closing p c w (hd.take fx) = .ok V)
    {pl : Place} {J : CloseJob (Local W₀ Rc Xi Tr)} (hJ : J.pub.par.k = P.k)
    {cc : (closePart (V := V') (X := X) (foldShellT true J foldWords)).Coins}
    (hcc : closeCoins (V := V') (X := X) Bk (Bk.rowsOf 0) (k.look 0) pl J = .ok cc)
    (hcodes : s.st.codes = p.sizes.codes)
    (hshape : ∀ y, s.st.oracles[D.m]? = some y →
      y.shape = ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape)
    (hq : seatBy noFirst s.book D.m = some (j, t)) (hnum : arr j t = num) (hfv : p.foldVars = P.k)
    (hbook : ∀ e ∈ Bk.ahead, (e.spender == ⟨pl, 0⟩) = true → e.once = true → e.owner = ⟨p.place, 0⟩ ∧
      e.start.e = (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)
          ((switchSent p.sizes p.others).size - 1)).e +
        fromE p.sizes.codes
          ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape)
    (W' : HIdx (sVars GE 2 ((stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g)) → GE)
    (hW : CoefOf (spentRun J (handSnd cc)) W') :
    Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W'
      (freshB D (K9.recOf s) (wordsFirst arr s.st s.book (Q.wit k w hd))) := by
  have hn : (switchSent p.sizes p.others).size - 1 < (switchSent p.sizes p.others).size := by omega
  have h1 := K2.Law.tab_rows_off Q Vd N 0 Dt readers closing p fx _ num j t hm hp hw hn k hH w hv hd hN hV
  obtain ⟨Wl, -, hR⟩ := K2.Law.rowsLaid_inv hV
  have hf : K2.foldAt (switchFresh p.sizes p.others p.foldVars) ((switchSent p.sizes p.others).size - 1) =
      some p.foldVars := by
    unfold K2.foldAt switchFresh
    show (if ((switchSent p.sizes p.others).size - 1 == (switchSent p.sizes p.others).size - 1) = true
      then some p.foldVars else none) = _
    rw [beq_self_eq_true]
    rfl
  obtain ⟨c₀, hc₀, hmask⟩ := sent_fresh_coins hR hn hf
  obtain ⟨y, hy₀, hrows, hcode⟩ := mask_code_of_base Hb
  have hy : s.st.oracles[D.m]? = some y := hy₀
  have hsh := hshape y hy
  have hk : P.k = (stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g :=
    Hb.stretch.trans (LeftIs.stageB_k Hb)
  have hlend : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender freshTable) p.sizes p.others p.foldVars p.carries) = .ok c := by
    unfold handed at hH
    cases hx : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
    | error e =>
      rw [hx] at hH
      cases hH
    | ok c2 =>
      rw [hx] at hH
      exact congrArg Except.ok (Option.some.inj hH)
  have hown := K12.Light.own_of_lendPart hlend
  refine fresh_of_sender Hb arr (Q.wit k w hd) hJ hcc hq (Vn := V ((switchSent p.sizes p.others).size - 1))
    (c₀ := c₀) (sender := ⟨p.place, 0⟩) ?_ ?_ ?_ hbook W' hW
  · intro y' hy'
    obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
    show (Q.wit k w hd).tab s.st.codes y.shape (arr j t) j t = _
    rw [hcodes, hsh, hnum]
    exact h1
  · intro b i hb hi
    have e1 : ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape.maskRows =
        2 ^ (stageB D (K9.recOf s)).h := by rw [← hsh]; exact hrows
    have hZ : (stageB D (K9.recOf s)).Z.l = (p.sizes.codes.mask.getD
        ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape.maskCode
        default).ell := by
      have hc1 : (D.S1 (K9.recOf s)).codes = s.st.codes :=
        (OnBytes.Means.extends_begun (K9.recOf s).st (K9.recOf s).frame.group D.G).codes
      show ((D.S1 (K9.recOf s)).codes.mask.getD (K9.recOf s).frame.shape.maskCode default).ell = _
      rw [hc1, hcodes, ← hsh, hcode]
    rw [hmask b i (by rw [e1]; exact hb) (by rw [← hZ]; exact hi), e1, ceilLog2_two_pow, hfv, hk]
  · intro t' ht
    have h2 := hc₀ t' (by rw [hfv, ← hJ]; exact ht)
    have h3 := K2.Reads.cut_eAt hown h2
    have h4 := (eAt_stretch _ h3).2
    rw [← h4]
    congr 1
    show 0 + _ = _
    omega

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mask_code_of_base
#print axioms ProofFile.Honest.K10.sent_fresh_coins
#print axioms ProofFile.Honest.K10.fresh_of_switch
