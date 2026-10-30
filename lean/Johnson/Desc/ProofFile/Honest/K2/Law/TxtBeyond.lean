-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TxtBeyond.lean: the kind "the code switch" (K2): WHAT THE LOT's
TEXT HOLDS WHERE THE SHAPE HAS NO ENTRY: at any message n of a switch's sending: a main entry beyond
the shape's rows or the code's length, and every mask entry where the shape has no mask row, is a
fixed public value: no data, no coin. Three statements with their proofs; no definition.

  `rowsAll_laid`       a sending's message n, read back in full: it is `laidRows` at four arrays
  `msgTxt_beyond`      the text at a main entry beyond the ranges
  `msgTxt_mask_bare`   the text at a mask entry, where the shape has no mask row

By: `rowsAll_at` (Honest/K2/Law/MaskCoin.lean) and `messageRows_laid` (Honest/K2/Law/Laid.lean): the
first · `rowsLaid_inv` (Honest/K2/Law/SenderOwn.lean), `msgTxt_rows` (Honest/K2/Law/MainTxt.lean),
and `laidRows`' own text (Laid.lean): the other two.

Limits. hH AND hV ARE PREMISES: that the switch is handed its stretches and lays its rows: where it
does not, the text answers nothing. ho is the very test that `laidRows` makes, said to fail. The
value beyond the ranges hangs on the shape's field alone: zero of the extension field, or the base
field's zero laid into it: that these two are one element is not said here. WHY: a tie on a Script's
message (`OwnMsgs`) asks its equation wherever a lot's text answers, and this text answers at every
place: so two texts that are to meet one number in the witness must agree here too. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (zeroG)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **A sending's message number n, read back in full.** -/
theorem rowsAll_laid {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)}
    {V : Nat → Johnson.Prover.Send.Rows}
    (h : rowsAll table codes sent fresh data c = .ok V) {n : Nat} (hn : n < sent.size) :
    ∃ (cF : Array Cb.Gl.F) (cE cM cT : Array Cb.Gl.E),
      V n = laidRows table codes (sent.getD n default).shape (foldAt fresh n) (data n) cF cE cM
        cT := by
  obtain ⟨c', -, hm⟩ := rowsAll_at h hn
  obtain ⟨-, -, -, cF, cE, cM, cT, -, -, -, -, e⟩ := messageRows_laid hm
  exact ⟨cF, cE, cM, cT, e⟩

/-- **Beyond the shape's rows or the code's length** the text's main entry is a value that hangs on
the field alone. -/
theorem msgTxt_beyond (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) {r j : Nat}
    (ho : (decide (r < ((switchSent p.sizes p.others).getD n default).shape.mainRows) &&
      decide (j < (p.sizes.codes.base.getD
        ((switchSent p.sizes p.others).getD n default).shape.code default).ell)) = false) :
    switchMsgTxt ch D readers closing p n k w hd false r j =
      some (if ((switchSent p.sizes p.others).getD n default).shape.mainDeg == 3 then zeroG
        else algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF 0)) := by
  obtain ⟨Wl, -, hR⟩ := rowsLaid_inv hV
  obtain ⟨cF, cE, cM, cT, e⟩ := rowsAll_laid hR hn
  rw [msgTxt_rows ch D readers closing p n k w hd hH hV false r j]
  show some ((V n).main (((switchSent p.sizes p.others).getD n default).shape.mainDeg == 3) r j) = _
  rw [e]
  unfold Johnson.Prover.Send.Rows.main laidRows
  simp only [ho, Bool.and_false, Bool.not_false, Bool.or_true, if_true]

/-- **Where the shape has no mask row** the text's mask entries are zero. -/
theorem msgTxt_mask_bare (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size)
    (hb : ((switchSent p.sizes p.others).getD n default).shape.maskRows = 0) (r j : Nat) :
    switchMsgTxt ch D readers closing p n k w hd true r j = some zeroG := by
  obtain ⟨Wl, -, hR⟩ := rowsLaid_inv hV
  obtain ⟨cF, cE, cM, cT, e⟩ := rowsAll_laid hR hn
  rw [msgTxt_rows ch D readers closing p n k w hd hH hV true r j]
  show some ((V n).mask r j) = _
  rw [e]
  unfold laidRows
  simp only [hb, Nat.not_lt_zero, decide_false, Bool.false_and, Bool.not_false, if_true]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.rowsAll_laid
#print axioms ProofFile.Honest.K2.Law.msgTxt_beyond
#print axioms ProofFile.Honest.K2.Law.msgTxt_mask_bare
