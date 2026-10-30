-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieBySwitch.lean: the closing of a segment (K10): `TiedRange` (Pay/XchTieRange.lean) at
the members that the code switch into the segment has sent (the carrying message, the kept copies, the segment's own messages of
moment 0), from one named record of premises.

  `TieBySwitch … seat`   the record. Its fields, by sort:
      on the script   msg, pad: the two ties at each message of the switch's sending but the last: its text off the pad; its pad's
      on the book     book: the entry by which the closing's part carries the message's coins is the switch's part's, at the
                      switch's own cut for the message · bookFront: the closing's part and the switch's part carry the coins of
                      the segments in front by entries of one owner, start and count, number by number
      public          chain, noWord; last (the last segment's sizes and first sending are the switch's); front (the segments in
                      front are the switch's); first (each of them has a message in its first sending); gam (their folds'
                      challenges have numbers below fx)
      at a stand      stand: the input is one that the ties speak of; enough challenges have been heard; the switch is handed its
                      coins and its rows are laid at the challenges in front of it; the statement's codes are the switch's; each
                      of these members has its seat and the switch's shape; the own main rows of the segments in front, and of
                      this segment's moment 0, are the same on both sides
  **`tied_by_switch`**   from the record: `TiedRange … 0 (the sending's messages less one)`

By: `tab_of_switch`, `coins_of_book`, `inFirst_at` (Pay/XchTieSwitch.lean); `data_of_switch` (Pay/XchTieData.lean);
`challenges_prefix`, `carried_same` (Pay/XchCongrPay.lean); `closingFrom_base` (Pay/XchTieKit.lean); `close_carried`
(Pay/XchLent.lean); `own_of_lendPart`, `carried_of_lendPart` (Honest/K12).

Limits. The record is a premise: a definition, shown here of no script, book, thread or run.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieRange
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieData
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchCongrPay
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieKit
import Johnson.Desc.ProofFile.Honest.K12.Sim.SenderInFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT seatBy noFirst)
open P5J (CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (SegmentPub SwitchPlace Stretch freshTable dueBefore messageDue switchSent switchFresh NoWord handed
  switchRowsLaid switchMsgOff switchPadTxt lotClosingAt ownBy)
open ProofFile.Honest.K2.Law (senderOwn Laid)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **What `TiedRange` takes at the members that the code switch into the segment has sent.** A definition, meant as a
premise. -/
structure TieBySwitch
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) (Zp : ProofFile.Pub)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace)
    (N fx : Nat) (seat : Nat → Nat × Nat) : Prop where
  /-- on the script -/
  msg : ∀ n, n + 1 < (switchSent p.sizes p.others).size →
    OwnMsgs Sc Vd N (P5J.At.arr Zp (seat n).1 (seat n).2) fx (switchMsgOff 0 rows readers (lotClosingAt lay segs) p n)
  pad : ∀ n, n + 1 < (switchSent p.sizes p.others).size →
    OwnPads Sc Vd (seat n).1 (seat n).2 (fun k _ => switchPadTxt 0 p n k)
  /-- on the book -/
  book : ∀ n, n + 1 < (switchSent p.sizes p.others).size → ∃ e, (K12.Light.carriedOf Bk ⟨blk.place, 0⟩)[
      0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (0 + n)]? = some e ∧
    e.owner = ⟨p.place, 0⟩ ∧
    e.start = dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n ∧
    e.count = messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
      (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n)
  bookFront : ∀ n, n < 0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum →
    ∃ e e', (K12.Light.carriedOf Bk ⟨blk.place, 0⟩)[n]? = some e ∧
      (K12.Light.carriedOf Bk ⟨p.place, 0⟩)[n]? = some e' ∧
      e.owner = e'.owner ∧ e.start = e'.start ∧ e.count = e'.count
  /-- public -/
  chain : T.chain = 0
  noWord : NoWord (switchSent p.sizes p.others)
  last : ∀ S, (lotSegs Zp Gr Qc).getLast? = some S →
    S.sizes = p.sizes ∧ S.sent.headD #[] = switchSent p.sizes p.others
  front : (lotSegs Zp Gr Qc).dropLast = segs.take p.link
  first : ∀ S ∈ (lotSegs Zp Gr Qc).dropLast, 0 < (S.sent.headD #[]).size
  gam : ∀ S ∈ (lotSegs Zp Gr Qc).dropLast, ∀ i ∈ S.gamma, i < fx
  /-- at a stand in front of an accepted closing -/
  stand : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D →
      Vd m.st.input ∧ N ≤ m.st.heard.length ∧ fx ≤ m.st.heard.length ∧
      (∃ c, handed 0 p k = some c ∧
        ∃ V, switchRowsLaid rows readers (lotClosingAt lay segs) p c m.st.input (m.st.heard.take fx) = .ok V) ∧
      s.st.codes = p.sizes.codes ∧
      (∀ n, n + 1 < (switchSent p.sizes p.others).size → ∀ o, D.G.members.idxOf? o = some (0 + n) →
        seatBy noFirst s.book o = some (seat n) ∧
          ∃ y, s.st.oracles[o]? = some y ∧ y.shape = ((switchSent p.sizes p.others).getD n default).shape) ∧
      (∀ i S, (lotSegs Zp Gr Qc).dropLast[i]? = some S →
        lotOwn readers rows Zp Gr Qc m.st.input m.st.heard (0 + i) =
          ownBy (rows m.st.input.x) (readers m.st.input) p.addrs
            (fun s m' => (((segs[s]?).map (·.ownShapes (s == 0))).getD []).getD m' {}) (m.st.heard.take fx) (0 + i)) ∧
      ∀ n, n + 1 < (switchSent p.sizes p.others).size → p.sizes.kept.length < n →
        lotOwn readers rows Zp Gr Qc m.st.input m.st.heard ((lotSegs Zp Gr Qc).length - 1)
            (n - 1 - p.sizes.kept.length) =
          senderOwn (rows m.st.input.x) (readers m.st.input) p (n - 1 - p.sizes.kept.length)

/-- **From the record: the witness's tables at these members are the rows that the closing's job has made anew.** -/
theorem tied_by_switch
    {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT} {Zp : ProofFile.Pub}
    {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {rows : RowDataOf ProofFile.Inst} {Gr : ProofFile.Ground}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : Nat} {Qc : Par} {blk : Block TS ProofFile.Cl}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {p : SwitchPlace}
    {N fx : Nat} {seat : Nat → Nat × Nat}
    (F : TieBySwitch T Sc Zp readers rows Gr Said l Qc blk Vd lay segs p N fx seat) (stAt : StAtOf ProofFile.Inst) :
    TiedRange T Sc Zp readers rows stAt Gr Said l Qc blk 0 ((switchSent p.sizes p.others).size - 1) := by
  intro k s m En ds y cols s' St D Hb cc hcc R hR hfit ds' o n a nn kk Rr hn hi hL hk hmsg
  have hn' : n + 1 < (switchSent p.sizes p.others).size := by omega
  obtain ⟨hv, hN, hfx, ⟨c, hH, V, hV⟩, hcodes, hseat, hown, hnow⟩ := F.stand St Hb
  obtain ⟨hq, y₀, hy, hsh⟩ := hseat n hn' o hi
  obtain ⟨S, x, hLast, hx, ha, rfl⟩ := hL
  obtain ⟨S', GR, hLast', -, rfl⟩ := lot_rows_inv readers rows stAt Zp Gr Qc _ _ _ hR
  obtain rfl : S = S' := Option.some.inj (hLast.symm.trans hLast')
  obtain ⟨hsz, hsent⟩ := F.last S hLast
  have hRc : (rowsOut S GR).codes = p.sizes.codes := congrArg (·.codes) hsz
  rw [F.chain] at hcc
  -- the member lies in the first sending
  have hA : (K2.Law.inFirstOf S (x.1.map (·.1))
      (lotOwn readers rows Zp Gr Qc m.st.input m.st.heard ((lotSegs Zp Gr Qc).length - 1)))[n]? = some a := by
    rw [Nat.zero_add, List.getElem?_append_left (by rw [inFirst_length, hsent]; exact hn)] at ha
    exact ha
  obtain ⟨ea1, -⟩ := inFirst_at S _ _ hA
  rw [hsent] at ea1
  -- the switch's own coins
  have hlend : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender freshTable) p.sizes p.others p.foldVars p.carries) = .ok c := by
    unfold handed at hH
    cases hz : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
    | error e =>
      rw [hz] at hH
      cases hH
    | ok c2 =>
      rw [hz] at hH
      exact congrArg Except.ok (Option.some.inj hH)
  have hownc := K12.Light.own_of_lendPart hlend
  have hcarK := close_carried hcc
  have hcarP : lend (k.look 0) p.carries (K12.Light.carriedOf Bk ⟨p.place, 0⟩) = .ok c.2.2 :=
    K12.Light.carried_of_lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender freshTable) p.sizes p.others p.foldVars p.carries) c hlend
  obtain ⟨e, he, ho, hs, hc⟩ := F.book n hn'
  rw [← closingFrom_base _ 0 0 none x hx] at he
  have htake : (m.st.heard ++ (ds ++ ds')).take fx = m.st.heard.take fx := List.take_append_of_le_length hfx
  have hlen : (m.st.heard.take fx).length = fx := by rw [List.length_take]; omega
  rw [hRc, ea1] at hmsg
  rw [tabAt_seat _ _ _ _ _ hq hy, hcodes, hsh, ea1]
  refine tab_of_switch Sc Vd N rows readers (lotClosingAt lay segs) p fx n _ _ _ (F.msg n hn') (F.pad n hn') F.noWord hn' k
    hH m.st.input hv (m.st.heard ++ (ds ++ ds')) (by rw [List.length_append]; omega) (by rw [htake]; exact hV) hmsg ?_
    (coins_of_book hcarK he ho hownc hs hc hk)
  intro Wl hW
  rw [htake, Nat.sub_zero, List.take_length] at hW
  refine data_of_switch hx hW F.front F.first hown (fun Sg hSg => ?_) (fun i _ hi' => ?_) hsz (hnow n hn') hA
  · have e0 : m.st.heard = m.st.heard.take fx ++ m.st.heard.drop fx := (List.take_append_drop fx _).symm
    conv_lhs => rw [e0]
    exact challenges_prefix _ _ _ fun i hi' => by rw [hlen]; exact F.gam Sg hSg i hi'
  · obtain ⟨e₁, e₂, h1, h2, q1, q2, q3⟩ := F.bookFront i hi'
    exact carried_same hcarK hcarP h1 h2 q1 q2 q3

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.TieBySwitch
#print axioms ProofFile.Honest.K10.tied_by_switch
