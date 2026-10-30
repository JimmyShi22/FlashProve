-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshShared.lean: the closing of a segment (K10): the pairing of the field fresh of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean) at a segment whose fresh mask the shared sending (the kind K1) has sent: the first
segment. The five clauses of `fresh_of_sender` (Pay/XchFreshJoin.lean), paid from the shared sending's own laws as far as these
reach.

  **`fresh_of_shared`**   the pairing. Its premises:
      hm, hp    the two ties on the script at the sender's message number n, at the shared sending's own texts
      hc        the sender's cut off the same look-up of coins as the closing's part is lent from
      hride     public: in message number n rides the table of a fold with the closing's count of row variables and the stage's
                count of row variables on the mask table
      hroom     public: the table's coins lie inside the sender's count
      hcodes, hshape, hq, hnum   public: the statement's codes are the sender's; the mask's message has the shape of the sender's
                message number n, the seat (j, t) and the number num in the witness
      hbook     on the book: an entry by which the closing's part spends is owned by the sender's part and starts where message
                number n's mask coins start among the sender's own (`K1.maskStart`, Honest/K1/MaskLaw.lean)

By: `tab_rows` (Honest/K1/ScriptTie.lean); `ride_coin` (Honest/K1/RideLaw.lean); `cut_at` (Honest/K12/CutOfBook.lean).

Limits. The premises are shown here of no script, book or run. No head and no thread is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshSwitch
import Johnson.Desc.ProofFile.Honest.K1.ScriptTie
import Johnson.Desc.ProofFile.Honest.K1.RideLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE)
open Cb (HIdx sVars)
open Johnson.Prover.Link (Pairs)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT wordsFirst seatBy noFirst)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open ProofFile.Honest.K10.LeftIs (stageB freshB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {V' W Wl X X' Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **The field fresh's pairing at a segment whose fresh mask the shared sending has sent.** -/
theorem fresh_of_shared {P : Par} {D : BaseData} {s : First.S} (Hb : CloseBase P (K9.recOf s) D)
    (arr : Nat → Nat → Nat) (Q : Script Bk Wl Cells Tok MsgT) (Vd : Wl → Prop) (N : Nat) (wit : Wl → W)
    (J : K1.SendJob W X) (own₀ : X) (front n num j t : Nat)
    (hm : OwnMsgs Q Vd N num front (K1.msgTxt 0 wit J own₀ n))
    (hp : OwnPads Q Vd j t (fun k _ => K1.padTxt 0 J n k))
    (k : Coins Bk) (c : Cs (K1.dueR J.P J.ride))
    (hc : K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    {pl : Place} {Jc : CloseJob Wl} (hJ : Jc.pub.par.k = P.k)
    {cc : (closePart (V := V') (X := X') (foldShellT true Jc foldWords)).Coins}
    (hcc : closeCoins (V := V') (X := X') Bk (Bk.rowsOf 0) (k.look 0) pl Jc = .ok cc)
    (hride : J.ride n = some ⟨P.k, (stageB D (K9.recOf s)).h⟩)
    (hroom : K1.maskStart J.P J.ride n + (2 * P.k + 1) ≤ (K1.dueR J.P J.ride).e)
    (hcodes : s.st.codes = J.P.codes)
    (hshape : ∀ y, s.st.oracles[D.m]? = some y → y.shape = shapeAt J.P n)
    (hq : seatBy noFirst s.book D.m = some (j, t)) (hnum : arr j t = num)
    (hbook : ∀ e ∈ Bk.ahead, (e.spender == ⟨pl, 0⟩) = true → e.once = true → e.owner = ⟨J.P.place, 0⟩ ∧
      e.start.e = K1.maskStart J.P J.ride n)
    (W' : HIdx (sVars GE 2 ((stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g)) → GE)
    (hW : CoefOf (spentRun Jc (handSnd cc)) W') :
    Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W'
      (freshB D (K9.recOf s) (wordsFirst arr s.st s.book (Q.wit k w hd))) := by
  have h1 := K1.tab_rows Q Vd N 0 wit J own₀ front n num j t hm hp k c hc w hw hd hN
  obtain ⟨y, hy₀, hrows, hcode⟩ := mask_code_of_base Hb
  have hy : s.st.oracles[D.m]? = some y := hy₀
  have hsh := hshape y hy
  have hk : P.k = (stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g :=
    Hb.stretch.trans (LeftIs.stageB_k Hb)
  refine fresh_of_sender Hb arr (Q.wit k w hd) hJ hcc hq
    (Vn := K1.rowsLaid J own₀ c (wit w) (hd.take front) n)
    (c₀ := fun i => if i < (⟨P.k, (stageB D (K9.recOf s)).h⟩ : K1.Ride).count then
      K1.ce c (K1.maskStart J.P J.ride n + i) else 0)
    (sender := ⟨J.P.place, 0⟩) ?_ ?_ ?_ hbook W' hW
  · intro y' hy'
    obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
    show (Q.wit k w hd).tab s.st.codes y.shape (arr j t) j t = _
    rw [hcodes, hsh, hnum]
    exact h1
  · intro b i hb hi
    have e1 : (shapeAt J.P n).maskRows = 2 ^ (stageB D (K9.recOf s)).h := by rw [← hsh]; exact hrows
    have hZ : (stageB D (K9.recOf s)).Z.l = (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell := by
      have hc1 : (D.S1 (K9.recOf s)).codes = s.st.codes :=
        (OnBytes.Means.extends_begun (K9.recOf s).st (K9.recOf s).frame.group D.G).codes
      show ((D.S1 (K9.recOf s)).codes.mask.getD (K9.recOf s).frame.shape.maskCode default).ell = _
      rw [hc1, hcodes, ← hsh, hcode]
    show (K1.rowsR J.P J.ride _ c n).mask b i = _
    rw [K1.ride_coin J.P J.ride _ c n b i _ hride (by rw [e1]; exact hb) (by rw [← hZ]; exact hi), hk]
  · intro t' ht
    have ht' : t' < 2 * P.k + 1 := by rw [← hJ]; exact ht
    have hcnt : t' < (⟨P.k, (stageB D (K9.recOf s)).h⟩ : K1.Ride).count := ht'
    show (if t' < (⟨P.k, (stageB D (K9.recOf s)).h⟩ : K1.Ride).count then
      K1.ce c (K1.maskStart J.P J.ride n + t') else 0) = _
    rw [if_pos hcnt]
    have hlt : K1.maskStart J.P J.ride n + t' < (K1.dueR J.P J.ride).e := by omega
    have h2 := K12.Light.cut_at (k.look 0 ⟨J.P.place, 0⟩).2 ⟨0, 0⟩ (K1.dueR J.P J.ride) c hc _ hlt
    have h3 : K1.ce c (K1.maskStart J.P J.ride n + t') =
        (K12.stretchOf c).e (K1.maskStart J.P J.ride n + t') := rfl
    rw [h3, h2]
    congr 1
    show 0 + _ = _
    omega

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.fresh_of_shared
