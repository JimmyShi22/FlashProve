-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshField.lean: the closing of a segment (K10): the field fresh of `CarryOwed`
(Honest/K10/Xch/CarryTop.lean), with the thread a letter, from one named record of premises for each of the two kinds that send
a fold's fresh mask.

  `FreshBySwitch`   the record at a segment whose fresh mask a code switch sends (segments 1 to 24). Its fields, by sort:
      on the script   msg, pad: the two ties at the switch's last message: its text off the pad; its pad's text
      on the book     book: the entry by which the closing's part spends is the switch's part's, from where the last message's
                      mask coins start
      public          chain (the thread is the first chain's), noWord, some, vars
      at a stand      stand: in front of an accepted closing: the input is one that the ties speak of; enough challenges have been
                      heard; the switch is handed its coins and its rows are laid at the challenges in front of it; the
                      statement's codes are the switch's; the fresh mask's message has the last message's shape and the seat
  `FreshByShared`   the like at a segment whose fresh mask the shared sending sends (segment 0), at its message number n
  **`fresh_by_switch`**, **`fresh_by_shared`**   from the record: the field, to the sign

By: `fresh_of_switch` (Pay/XchFreshSwitch.lean); `fresh_of_shared` (Pay/XchFreshShared.lean).

Limits. The records are premises: definitions, shown here of no script, book, thread or run.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshShared
import Johnson.Desc.ProofFile.Honest.K10.Thr.HalfOfLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE)
open Johnson.Prover.Link (Pairs)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT wordsFirst seatBy noFirst)
open P5J (CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (SwitchPlace Closing fromE dueBefore switchSent switchFresh NoWord handed switchRowsLaid switchMsgOff
  switchPadTxt)
open ProofFile.Honest.K10.LeftIs (stageB freshB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **What the field fresh takes at a segment whose fresh mask a code switch sends.** A definition, meant as a premise. -/
structure FreshBySwitch (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) (Zp : ProofFile.Pub)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (closing : Closing) (p : SwitchPlace) (N fx j t : Nat) : Prop where
  /-- on the script: the message at the witness's number of the seat is the switch's last message's text, off the pad -/
  msg : OwnMsgs Sc Vd N (P5J.At.arr Zp j t) fx
    (switchMsgOff 0 rows readers closing p ((switchSent p.sizes p.others).size - 1))
  /-- on the script: the pad at the seat is the switch's -/
  pad : OwnPads Sc Vd j t (fun k _ => switchPadTxt 0 p ((switchSent p.sizes p.others).size - 1) k)
  /-- on the book -/
  book : ∀ e ∈ Bk.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true → e.owner = ⟨p.place, 0⟩ ∧
    e.start.e = (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)
        ((switchSent p.sizes p.others).size - 1)).e +
      fromE p.sizes.codes
        ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape
  /-- public -/
  chain : T.chain = 0
  noWord : NoWord (switchSent p.sizes p.others)
  some : 0 < (switchSent p.sizes p.others).size
  vars : p.foldVars = Qc.k
  /-- at a stand in front of an accepted closing -/
  stand : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D →
      Vd m.st.input ∧ N ≤ m.st.heard.length ∧ fx ≤ m.st.heard.length ∧
      (∃ c, handed 0 p k = Option.some c ∧
        ∃ V, switchRowsLaid rows readers closing p c m.st.input (m.st.heard.take fx) = .ok V) ∧
      s.st.codes = p.sizes.codes ∧
      (∀ y, s.st.oracles[D.m]? = Option.some y →
        y.shape = ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape) ∧
      seatBy noFirst s.book D.m = Option.some (j, t)

/-- **The field fresh, from the record at a code switch.** -/
theorem fresh_by_switch {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT} {Zp : ProofFile.Pub}
    {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {rows : RowDataOf ProofFile.Inst}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : Nat} {Qc : Par} {blk : Block TS ProofFile.Cl}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {closing : Closing} {p : SwitchPlace} {N fx j t : Nat}
    (F : FreshBySwitch T Sc Zp readers rows Said l Qc blk Vd closing p N fx j t) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) :
    ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ ds' W, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) W →
      Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
        (freshB D (K9.recOf s)
          (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))))) := by
  intro k s m En ds y cols s' St D Hb cc hcc ds' W hW
  obtain ⟨hv, hN, hfx, ⟨c, hH, V, hV⟩, hcodes, hshape, hq⟩ := F.stand St Hb
  rw [F.chain] at hcc
  exact fresh_of_switch Hb (P5J.At.arr Zp) Sc Vd N rows readers closing p fx _ j t F.msg F.pad F.noWord F.some k hH
    m.st.input hv (m.st.heard ++ (ds ++ ds')) (by rw [List.length_append]; omega)
    (by rw [List.take_append_of_le_length hfx]; exact hV) rfl hcc hcodes hshape hq rfl F.vars F.book W hW

/-- **What the field fresh takes at a segment whose fresh mask the shared sending sends**, as its message number n. A
definition, meant as a premise. -/
structure FreshByShared {Wj Xj : Type}
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) (Zp : ProofFile.Pub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (J : K1.SendJob Wj Xj) (own₀ : Xj)
    (N front n j t : Nat) : Prop where
  /-- on the script -/
  msg : OwnMsgs Sc Vd N (P5J.At.arr Zp j t) front (K1.msgTxt 0 wit J own₀ n)
  pad : OwnPads Sc Vd j t (fun k _ => K1.padTxt 0 J n k)
  /-- on the book -/
  book : ∀ e ∈ Bk.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true → e.owner = ⟨J.P.place, 0⟩ ∧
    e.start.e = K1.maskStart J.P J.ride n
  /-- public -/
  chain : T.chain = 0
  room : K1.maskStart J.P J.ride n + (2 * Qc.k + 1) ≤ (K1.dueR J.P J.ride).e
  /-- at a stand in front of an accepted closing -/
  stand : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D →
      Vd m.st.input ∧ N ≤ m.st.heard.length ∧
      (∃ c, K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = Option.some c) ∧
      J.ride n = Option.some ⟨Qc.k, (stageB D (K9.recOf s)).h⟩ ∧
      s.st.codes = J.P.codes ∧
      (∀ y, s.st.oracles[D.m]? = Option.some y → y.shape = shapeAt J.P n) ∧
      seatBy noFirst s.book D.m = Option.some (j, t)

/-- **The field fresh, from the record at the shared sending.** -/
theorem fresh_by_shared {Wj Xj : Type}
    {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT} {Zp : ProofFile.Pub}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : Nat} {Qc : Par} {blk : Block TS ProofFile.Cl}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {wit : Local W₀ Rc ProofFile.Inst Tr → Wj} {J : K1.SendJob Wj Xj} {own₀ : Xj}
    {N front n j t : Nat} (F : FreshByShared T Sc Zp Said l Qc blk Vd wit J own₀ N front n j t)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) :
    ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ ds' W, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) W →
      Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
        (freshB D (K9.recOf s)
          (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))))) := by
  intro k s m En ds y cols s' St D Hb cc hcc ds' W hW
  obtain ⟨hv, hN, ⟨c, hc⟩, hride, hcodes, hshape, hq⟩ := F.stand St Hb
  rw [F.chain] at hcc
  exact fresh_of_shared Hb (P5J.At.arr Zp) Sc Vd N wit J own₀ front n _ j t F.msg F.pad k c hc m.st.input hv
    (m.st.heard ++ (ds ++ ds')) (by rw [List.length_append]; omega) rfl hcc hride F.room hcodes hshape hq rfl F.book W hW

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.FreshBySwitch
#print axioms ProofFile.Honest.K10.fresh_by_switch
#print axioms ProofFile.Honest.K10.FreshByShared
#print axioms ProofFile.Honest.K10.fresh_by_shared
