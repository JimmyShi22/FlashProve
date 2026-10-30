-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PadTxt.lean: the kind "the code switch" (K2): WHAT THE LOT's
TEXT `switchMsgTxt` (Honest/K2/ScriptLots.lean) ANSWERS AT A PAD's PLACE IN A MAIN ROW: WHICH COIN
OF THE PART's OWN STANDS THERE, BY NUMBER: the sister of Honest/K2/Law/MainTxt.lean, which speaks
off these places. Statements with their proofs: joins; no definition.

  `laidPad_e`, `laidPad_f`   tools: the two fields of V n at the pad's place number i, by the shared
                 sending's total readers
  `padNumber_e`, `padNumber_f`   THE NUMBER LIES WITHIN THE COUNT
  `msgTxt_pad_e`, `msgTxt_pad_f`   THE ENDS, where the part is handed c and the rows are laid: THE
                 READER THAT REFUSES BEYOND THE COUNT (`Cs.eAt`, `Cs.fAt`, Honest/Frame.lean)
                 returns x at that number of c.1, and the text's answer there is made of x
  `msgTxt_pad_e_of`, `msgTxt_pad_f_of`   the same for whoever holds an answer y alone: the part's
                 own coins cs are there (`K1.lentCut`), and that reader returns at that number

THE PLACE: the last main row, place ell - T.pad + i, i below T.pad: T := `K1.stepsOf` at the
message's shape (Honest/K1/Coins.lean): the shared sending's own counts: T.pad is 0 at a message
with a mask row or without a sample. THE NUMBER: a + (T.tails + i): the message's start a in the
sending (`dueBefore`, Honest/K2/Part.lean), then the tails of its main rows, then i: among the coins
of the extension field where the message's rows are over it; else among those of the base field,
embedded. AT ANY MESSAGE n OF THE SENDING: the carrying message and the kept copies too.

By: the shared sending's `pad_coin_e`, `pad_coin_f` (Honest/K1/CoinLaw.lean) and `main_coin_e`,
`main_coin_f` (Honest/K1/CoinsIn.lean), of other authors, carried to this kind's rows by
`rowsAll_shared_paid` (Honest/K2/Law/SameRows.lean); `dueBefore_shared`, `sendingDue_shared`,
`shapeFits_of` (Honest/K2/Law/Counts.lean); `ce_cast`, `cf_cast` (Honest/K2/Law/Room.lean);
`own_of_handed`, `rows_of_laid` (Honest/K2/Law/MaskTxt.lean); `msgTxt_rows`, `msgTxt_inv`
(MainTxt.lean).

Limits. That the text answers at all is a premise. `NoWord` is a premise (under the opening:
`noWord_open`, Honest/K2/Law/SampledOpen.lean, not imported). THAT THESE PLACES ARE JUST
`padInMain`'s MEMBERS (the fence of MainTxt.lean), and, at one answer and below ell, just those at
which `padB` says yes, is not said here: Honest/K2/Law/PadPlaces.lean, which this file does not
import, says it. THE SUBTRACTION ell - T.pad STOPS AT 0: at a shape whose pad is longer than ell the
places spoken of run beyond ell: a matter of the public numbers; where `rowsAll` returns it does not
arise (`shapeFits_of`: T.pad is at most ell), and the statements do not say so. Nothing on the rows'
tails, nor on a message without a sample. WHICH COIN IS WRITTEN WHERE: no sentence on what a coin is
for. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.Room
import Johnson.Desc.ProofFile.Honest.K1.CoinLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open Reads

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

section
variable {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
  {fresh : Option (Nat × Nat)} {data : Nat → Nat → Nat → Cb.Gl.E}
  {c : Cs (sendingDue codes sent fresh)} {V : Nat → Johnson.Prover.Send.Rows}

/-- The pad's place number i, over the extension field. s: the message's shape. T: the shared
sending's counts at it. a: its start in the sending. ell: its code's message length. -/
theorem laidPad_e (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n : Nat} (hn : n < sent.size) {s : OnBytes.OracleShape}
    (hs : (sent.getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf codes s (rideOf sent fresh n) = T) {a : Due}
    (hA : dueBefore codes sent fresh n = a) {ell : Nat}
    (hl : (codes.base.getD s.code default).ell = ell) {i : Nat}
    (h3 : (s.mainDeg == 3) = true) (ha : s.answers ≠ 0) (hm : 0 < s.mainRows) (hi : i < T.pad) :
    (V n).mainE (s.mainRows - 1) (ell - T.pad + i) = K1.ce c (a.e + (T.tails + i)) := by
  subst hs hT hA hl
  have hf := rowsAll_fits h
  have e := sendingPar_shape codes sent n
  have hp := (shapeFits_of (fresh := fresh) hf hn).pad
  rw [← rideOf_as] at hp
  rw [rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h hn,
    dueBefore_shared hf hw n (Nat.le_of_lt hn)]
  have key := K1.pad_coin_e (sendingPar codes sent) (rideOf sent fresh) (dataShared sent data)
    (cs := sendingDue_shared hf hw ▸ c) (k := n) i (by rw [e]; exact h3) (by rw [e]; exact ha)
    (by rw [e]; exact hm) (by rw [e]; exact hp) (by rw [e]; exact hi)
  rw [e, ce_cast] at key
  exact key

/-- The like over the base field. -/
theorem laidPad_f (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n : Nat} (hn : n < sent.size) {s : OnBytes.OracleShape}
    (hs : (sent.getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf codes s (rideOf sent fresh n) = T) {a : Due}
    (hA : dueBefore codes sent fresh n = a) {ell : Nat}
    (hl : (codes.base.getD s.code default).ell = ell) {i : Nat}
    (h3 : (s.mainDeg == 3) = false) (ha : s.answers ≠ 0) (hm : 0 < s.mainRows) (hi : i < T.pad) :
    (V n).mainF (s.mainRows - 1) (ell - T.pad + i) = K1.cf c (a.f + (T.tails + i)) := by
  subst hs hT hA hl
  have hf := rowsAll_fits h
  have e := sendingPar_shape codes sent n
  have hp := (shapeFits_of (fresh := fresh) hf hn).pad
  rw [← rideOf_as] at hp
  rw [rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h hn,
    dueBefore_shared hf hw n (Nat.le_of_lt hn)]
  have key := K1.pad_coin_f (sendingPar codes sent) (rideOf sent fresh) (dataShared sent data)
    (cs := sendingDue_shared hf hw ▸ c) (k := n) i (by rw [e]; exact h3) (by rw [e]; exact ha)
    (by rw [e]; exact hm) (by rw [e]; exact hp) (by rw [e]; exact hi)
  rw [e, cf_cast] at key
  exact key

/-- **THE NUMBER LIES WITHIN THE COUNT**, over the extension field. -/
theorem padNumber_e (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n : Nat} (hn : n < sent.size) {s : OnBytes.OracleShape}
    (hs : (sent.getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf codes s (rideOf sent fresh n) = T) {a : Due}
    (hA : dueBefore codes sent fresh n = a) {i : Nat}
    (h3 : (s.mainDeg == 3) = true) (hi : i < T.pad) :
    a.e + (T.tails + i) < (sendingDue codes sent fresh).e := by
  subst hs hT hA
  have hf := rowsAll_fits h
  have e := sendingPar_shape codes sent n
  rw [dueBefore_shared hf hw n (Nat.le_of_lt hn), sendingDue_shared hf hw]
  refine K1.main_coin_e (sendingPar codes sent) (rideOf sent fresh) n _
    (by rw [sendingPar_sent]; exact hn) (by rw [e]; exact h3) ?_
  rw [e]
  show _ < (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).tails +
    (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).word +
    (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).pad
  omega

/-- The like over the base field. -/
theorem padNumber_f (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n : Nat} (hn : n < sent.size) {s : OnBytes.OracleShape}
    (hs : (sent.getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf codes s (rideOf sent fresh n) = T) {a : Due}
    (hA : dueBefore codes sent fresh n = a) {i : Nat}
    (h3 : (s.mainDeg == 3) = false) (hi : i < T.pad) :
    a.f + (T.tails + i) < (sendingDue codes sent fresh).f := by
  subst hs hT hA
  have hf := rowsAll_fits h
  have e := sendingPar_shape codes sent n
  rw [dueBefore_shared hf hw n (Nat.le_of_lt hn), sendingDue_shared hf hw]
  refine K1.main_coin_f (sendingPar codes sent) (rideOf sent fresh) n _
    (by rw [sendingPar_sent]; exact hn) (by rw [e]; exact h3) ?_
  rw [e]
  show _ < (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).tails +
    (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).word +
    (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).pad
  omega

end

/-- **THE END, OVER THE EXTENSION FIELD.** n: any message of the sending. The letters s, T, a, ell:
as above: public. THE READER REFUSES BEYOND THE COUNT: it returns x: so a coin stands there. -/
theorem msgTxt_pad_e (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) {s : OnBytes.OracleShape}
    (hs : ((switchSent p.sizes p.others).getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf p.sizes.codes s (rideOf (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n) = T) {a : Due}
    (hA : dueBefore p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n = a) {ell : Nat}
    (hl : (p.sizes.codes.base.getD s.code default).ell = ell) {i : Nat}
    (h3 : (s.mainDeg == 3) = true) (ha : s.answers ≠ 0) (hm : 0 < s.mainRows) (hi : i < T.pad) :
    ∃ x, c.1.eAt (a.e + (T.tails + i)) = .ok x ∧
      switchMsgTxt ch D readers closing p n k w hd false (s.mainRows - 1) (ell - T.pad + i) =
        some x := by
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  have hb := padNumber_e hw hR hn hs hT hA h3 hi
  refine ⟨_, eAt_of_lt c.1 hb, ?_⟩
  rw [msgTxt_rows ch D readers closing p n k w hd hH hV false, hs]
  show some ((V n).main (s.mainDeg == 3) _ _) = _
  unfold Johnson.Prover.Send.Rows.main
  rw [if_pos h3, laidPad_e hw hR hn hs hT hA hl h3 ha hm hi]
  unfold K1.ce
  rw [dif_pos hb]

/-- **THE END, OVER THE BASE FIELD.** -/
theorem msgTxt_pad_f (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) {s : OnBytes.OracleShape}
    (hs : ((switchSent p.sizes p.others).getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf p.sizes.codes s (rideOf (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n) = T) {a : Due}
    (hA : dueBefore p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n = a) {ell : Nat}
    (hl : (p.sizes.codes.base.getD s.code default).ell = ell) {i : Nat}
    (h3 : (s.mainDeg == 3) = false) (ha : s.answers ≠ 0) (hm : 0 < s.mainRows) (hi : i < T.pad) :
    ∃ x, c.1.fAt (a.f + (T.tails + i)) = .ok x ∧
      switchMsgTxt ch D readers closing p n k w hd false (s.mainRows - 1) (ell - T.pad + i) =
        some (algebraMap Cb.Gl.F Cb.Gl.E x) := by
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  have hb := padNumber_f hw hR hn hs hT hA h3 hi
  refine ⟨_, fAt_of_lt c.1 hb, ?_⟩
  rw [msgTxt_rows ch D readers closing p n k w hd hH hV false, hs]
  show some ((V n).main (s.mainDeg == 3) _ _) = _
  unfold Johnson.Prover.Send.Rows.main
  rw [if_neg (by rw [h3]; exact Bool.false_ne_true), laidPad_f hw hR hn hs hT hA hl h3 ha hm hi]
  unfold K1.cf
  rw [dif_pos hb]

/-- **THE SAME, FOR WHOEVER HOLDS AN ANSWER ALONE**, over the extension field. -/
theorem msgTxt_pad_e_of (ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) {s : OnBytes.OracleShape}
    (hs : ((switchSent p.sizes p.others).getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf p.sizes.codes s (rideOf (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n) = T) {a : Due}
    (hA : dueBefore p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n = a) {ell : Nat}
    (hl : (p.sizes.codes.base.getD s.code default).ell = ell) {i : Nat}
    (h3 : (s.mainDeg == 3) = true) (ha : s.answers ≠ 0) (hm : 0 < s.mainRows) (hi : i < T.pad)
    {y : Cb.Gl.E}
    (hy : switchMsgTxt ch D readers closing p n k w hd false (s.mainRows - 1) (ell - T.pad + i) =
      some y) :
    ∃ cs, K1.lentCut k ch ⟨p.place, 0⟩ (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) = some cs ∧
      cs.eAt (a.e + (T.tails + i)) = .ok y := by
  obtain ⟨c, V, hH, hV⟩ := msgTxt_inv hy
  obtain ⟨x, hx1, hx2⟩ :=
    msgTxt_pad_e ch D readers closing p k w hd hH hV hw hn hs hT hA hl h3 ha hm hi
  obtain rfl : x = y := Option.some.inj (hx2.symm.trans hy)
  exact ⟨c.1, own_of_handed ch p k c hH, hx1⟩

/-- The like over the base field. -/
theorem msgTxt_pad_f_of (ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) {s : OnBytes.OracleShape}
    (hs : ((switchSent p.sizes p.others).getD n default).shape = s) {T : K1.Steps}
    (hT : K1.stepsOf p.sizes.codes s (rideOf (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n) = T) {a : Due}
    (hA : dueBefore p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n = a) {ell : Nat}
    (hl : (p.sizes.codes.base.getD s.code default).ell = ell) {i : Nat}
    (h3 : (s.mainDeg == 3) = false) (ha : s.answers ≠ 0) (hm : 0 < s.mainRows) (hi : i < T.pad)
    {y : Cb.Gl.E}
    (hy : switchMsgTxt ch D readers closing p n k w hd false (s.mainRows - 1) (ell - T.pad + i) =
      some y) :
    ∃ cs x, K1.lentCut k ch ⟨p.place, 0⟩ (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) = some cs ∧
      cs.fAt (a.f + (T.tails + i)) = .ok x ∧ y = algebraMap Cb.Gl.F Cb.Gl.E x := by
  obtain ⟨c, V, hH, hV⟩ := msgTxt_inv hy
  obtain ⟨x, hx1, hx2⟩ :=
    msgTxt_pad_f ch D readers closing p k w hd hH hV hw hn hs hT hA hl h3 ha hm hi
  exact ⟨c.1, x, own_of_handed ch p k c hH, hx1, (Option.some.inj (hx2.symm.trans hy)).symm⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.laidPad_e
#print axioms ProofFile.Honest.K2.Law.laidPad_f
#print axioms ProofFile.Honest.K2.Law.padNumber_e
#print axioms ProofFile.Honest.K2.Law.padNumber_f
#print axioms ProofFile.Honest.K2.Law.msgTxt_pad_e
#print axioms ProofFile.Honest.K2.Law.msgTxt_pad_f
#print axioms ProofFile.Honest.K2.Law.msgTxt_pad_e_of
#print axioms ProofFile.Honest.K2.Law.msgTxt_pad_f_of
