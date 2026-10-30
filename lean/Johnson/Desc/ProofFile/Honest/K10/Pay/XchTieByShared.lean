-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieByShared.lean: the closing of a segment (K10): `TiedRange` (Pay/XchTieRange.lean) at
the members that one sending of the shared kind (K1) has sent, from one named record of premises.

  `TieByShared … lo cnt seat`   the record: the sender's messages 0, …, cnt − 1 are the group's members at the places lo, …. Its
      fields, by sort:
      on the script   msg, pad: the two ties at each of these messages, at the shared sending's own texts
      on the book     book: the entry by which the closing's part carries the message's coins is the sender's part's, starts where
                      the sender's text takes the message's coins, and lies inside the sender's count
      public          chain; ride, padOk, word (of each message: no table rides; the pad is no longer than a row; it has no main
                      row or is sampled); codes (the last segment's codes are the sender's)
      at a stand      stand: the input is one that the ties speak of; enough challenges have been heard; the sender has its cut;
                      the statement's codes are the sender's; each of these members has its seat and the sender's shape; the
                      job's shape and data for it are the sender's, read as a row of its field takes them
  **`tied_by_shared`**   from the record: `TiedRange … lo cnt`

By: `tab_of_shared` (Pay/XchTieShared.lean); `carried_in_own`, `closingFrom_base` (Pay/XchTieKit.lean); `close_carried`
(Pay/XchLent.lean); `tabAt_seat` (Pay/XchTieRows.lean).

Limits. The record is a premise: a definition, shown here of no script, book, thread or run.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieRange
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieShared
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT seatBy noFirst)
open P5J (CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (asRow)
open ProofFile.Honest.K2.Law (Laid)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **What `TiedRange` takes at the members that one sending of the shared kind has sent.** A definition, meant as a
premise. -/
structure TieByShared {Wj Xj : Type}
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) (Zp : ProofFile.Pub)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (J : K1.SendJob Wj Xj) (own₀ : Xj)
    (N front lo cnt : Nat) (seat : Nat → Nat × Nat) : Prop where
  /-- on the script -/
  msg : ∀ n, n < cnt → OwnMsgs Sc Vd N (P5J.At.arr Zp (seat n).1 (seat n).2) front (K1.msgTxt 0 wit J own₀ n)
  pad : ∀ n, n < cnt → OwnPads Sc Vd (seat n).1 (seat n).2 (fun k _ => K1.padTxt 0 J n k)
  /-- on the book -/
  book : ∀ n, n < cnt → ∃ e, (K12.Light.carriedOf Bk ⟨blk.place, 0⟩)[
      0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (lo + n)]? = some e ∧
    e.owner = ⟨J.P.place, 0⟩ ∧ e.start = K1.startR J.P J.ride n ∧
    e.start.f + e.count.f ≤ (K1.dueR J.P J.ride).f ∧ e.start.e + e.count.e ≤ (K1.dueR J.P J.ride).e
  /-- public -/
  chain : T.chain = 0
  ride : ∀ n, n < cnt → J.ride n = none
  padOk : ∀ n, n < cnt → (K1.stepsOf J.P.codes (shapeAt J.P n) none).pad ≤
    (J.P.codes.base.getD (shapeAt J.P n).code default).ell
  word : ∀ n, n < cnt → (shapeAt J.P n).mainRows = 0 ∨ (shapeAt J.P n).answers ≠ 0
  codes : ∀ S, (lotSegs Zp Gr Qc).getLast? = some S → S.sizes.codes = J.P.codes
  /-- at a stand in front of an accepted closing -/
  stand : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D →
      Vd m.st.input ∧ N ≤ m.st.heard.length ∧ front ≤ m.st.heard.length ∧
      (∃ c, K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c) ∧
      s.st.codes = J.P.codes ∧
      (∀ n, n < cnt → ∀ o, D.G.members.idxOf? o = some (lo + n) →
        seatBy noFirst s.book o = some (seat n) ∧ ∃ y, s.st.oracles[o]? = some y ∧ y.shape = shapeAt J.P n) ∧
      ∀ n, n < cnt → ∀ (ca : CsAll (closeCarries ⟨Qc, borneAt Zp Qc⟩)) (a : Laid) (nn : Nat),
        LotMember readers rows Zp Gr Qc m.st.input m.st.heard ca (lo + n) a nn →
        a.1 = shapeAt J.P n ∧ a.2 = fun r i => asRow ((shapeAt J.P n).mainDeg == 3)
          (J.data (wit m.st.input) { heard := m.st.heard.take front, own := own₀, seen := .bare [] } n r i)

/-- **From the record: the witness's tables at these members are the rows that the closing's job has made anew.** -/
theorem tied_by_shared {Wj Xj : Type}
    {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT} {Zp : ProofFile.Pub}
    {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {rows : RowDataOf ProofFile.Inst} {Gr : ProofFile.Ground}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : Nat} {Qc : Par} {blk : Block TS ProofFile.Cl}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {wit : Local W₀ Rc ProofFile.Inst Tr → Wj} {J : K1.SendJob Wj Xj} {own₀ : Xj}
    {N front lo cnt : Nat} {seat : Nat → Nat × Nat}
    (F : TieByShared T Sc Zp readers rows Gr Said l Qc blk Vd wit J own₀ N front lo cnt seat)
    (stAt : StAtOf ProofFile.Inst) : TiedRange T Sc Zp readers rows stAt Gr Said l Qc blk lo cnt := by
  intro k s m En ds y cols s' St D Hb cc hcc R hR hfit ds' o n a nn kk Rr hn hi hL hk hmsg
  obtain ⟨hv, hN, hfr, ⟨c, hc⟩, hcodes, hseat, hdata⟩ := F.stand St Hb
  obtain ⟨hq, y₀, hy, hsh⟩ := hseat n hn o hi
  obtain ⟨ea1, ea2⟩ := hdata n hn _ a nn hL
  obtain ⟨S, x, hLast, hx, -, rfl⟩ := hL
  obtain ⟨S', GR, hLast', -, rfl⟩ := lot_rows_inv readers rows stAt Zp Gr Qc _ _ _ hR
  obtain rfl : S = S' := Option.some.inj (hLast.symm.trans hLast')
  have hRc : (rowsOut S GR).codes = J.P.codes := F.codes S hLast
  rw [F.chain] at hcc
  obtain ⟨e, he, ho, hs, hbf, hbe⟩ := F.book n hn
  rw [← closingFrom_base _ 0 0 none x hx] at he
  have h1 : (k.look 0 e.owner).2.cut ⟨0, 0⟩ (K1.dueR J.P J.ride) = some c := by
    rw [ho]
    exact hc
  obtain ⟨c', hcut, hcar⟩ := carried_in_own (close_carried hcc) he h1 hbf hbe
  have hkk : kk = ⟨e.count, c'⟩ := Except.ok.inj (hk.symm.trans hcar)
  rw [hs] at hcut
  rw [hRc, ea1] at hmsg
  rw [tabAt_seat _ _ _ _ _ hq hy, hcodes, hsh, ea1]
  refine tab_of_shared Sc Vd N wit J own₀ front n _ _ _ (F.msg n hn) (F.pad n hn) k c hc m.st.input hv
    (m.st.heard ++ (ds ++ ds')) (by rw [List.length_append]; omega) hmsg hcut hkk ?_ (F.ride n hn) (F.padOk n hn)
    (F.word n hn)
  rw [List.take_append_of_le_length hfr]
  exact ea2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.TieByShared
#print axioms ProofFile.Honest.K10.tied_by_shared
