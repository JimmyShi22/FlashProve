-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Column.lean: THE LIBRARY'S HONEST TABLE HAS, AT EVERY POSITION, THE RUNNING COMMITTER'S
COLUMN. The proofs of four statements of Johnson/Bind/ColumnDefs.lean, general in the sizes.

How. Both sides encode a row with `Fmt.M1.symF`, and a symbol depends on the message's and the
tail's words through their residues modulo the prime alone (`Bind.Twin.symF_congr`,
Johnson/Bind/TwinFitted.lean). So it is enough that, row by row, the two sides' lists have the same
residues. The library's road from words to the field and back (`honestMsgs`, then `rowWords`) turns
each word into its residue (`ofF_toF`, `rowsResidues`). Before the pads both sides have the
library's own word of the matrix's cell; from the pads on the library has the residue of the raw pad
and the running committer the raw pad; the tails likewise.

Main names (namespace `Bind.Column`).
  `ofF_toF`: a word, read in the field and written again, is its residue.
  `rowsResidues S`, `rowsBack S`: `RowsResidues S`, `RowsBack S`: no premise.
  `message_agrees`, `tail_agrees`: a row's two messages, and its two tails, have the same residues.
  **`columnAgrees`**: `ColumnAgrees S Z cut N sh`, if the shape has the sizes' numbers (`Agree`).
  `ok_columnOf`, `length_columnOf`: every word of the running committer's column is below the prime,
    and there is one for each row.
  `encIsHonestTab`: `EncIsHonestTab S Z cut N`: by unfolding.

WHO READS EACH LETTER. S: both sides (through `Agree` on the running committer's). cut: where the
pads begin, on both sides. N, Z: the library's words of a cell alone; the same term stands on both
sides. M, tail, pad, salt, the position: under "for all". No premise is asked of a raw word: a tail
or a pad from the prime on is covered. The salt is read by neither side here.

Limits. Those of Johnson/Bind/ColumnDefs.lean. That `Agree` is met at the two sizes is shown in
Johnson/Bind/ColumnSizes.lean. Rows beyond the table's last and positions beyond the code's length
are not spoken of.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.ColumnDefs
import Johnson.Bind.TwinFitted

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Column
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open Bind.Twin (Shape Table residue residue_residue residue_of_ok symF_congr)

/-! ## Words -/

/-- A word, read in the field and written again, is its residue modulo the prime. -/
theorem ofF_toF (w : UInt64) : OnBytes.Slice.ofF (OnBytes.Slice.toF w) = residue w := by
  have h : ((w.toNat : Cb.Gl.F)).val = w.toNat % Code.pGold := ZMod.val_natCast ..
  show UInt64.ofNat ((w.toNat : Cb.Gl.F)).val = UInt64.ofNat (w.toNat % Fmt.Fld.two.p)
  rw [h, two_p]

/-- Read in the field and written again, a row's words come back as residues. -/
theorem rowsResidues (S : Sz) : RowsResidues S := by
  intro msg b hb
  have hr : Sz.rowNo (fun t : Fin S.P.v => b.testBit t.val) = b := by
    rw [rowNo_testBit, Nat.mod_eq_of_lt hb]
  refine List.ext_getElem ?_ fun j h1 h2 => ?_
  · unfold rowWords rowWordsAt
    rw [List.length_ofFn, List.length_map, List.length_range]
  · unfold rowWords rowWordsAt
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    show OnBytes.Slice.ofF (OnBytes.Slice.toF
      ((msg (Sz.rowNo fun t : Fin S.P.v => b.testBit t.val)).getD j 0)) = _
    rw [hr, ofF_toF]

/-- A message's length of words below the prime comes back as it is. -/
theorem rowsBack (S : Sz) : RowsBack S := by
  intro msg b hb hl hok
  rw [rowsResidues S msg b hb]
  refine List.ext_getElem ?_ fun j h1 h2 => ?_
  · rw [List.length_map, List.length_range, hl]
  · simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h2]
    exact residue_of_ok _ (hok _ (List.getElem_mem h2))

/-! ## The library's word of a cell -/

section
variable (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)

/-- Before the pads an entry does not feel the pads. -/
theorem cellEntry_before (M : Cells (S.toDecR Z cut) N) (η η' : PadsOf S cut) (b e : ℕ)
    (hc : e < cut) : cellEntry S Z cut N M η b e = cellEntry S Z cut N M η' b e := by
  unfold cellEntry cellEntryAt
  rw [if_pos hc, if_pos hc]

/-- From the pads on an entry is the pad's word. -/
theorem cellEntry_pad (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (b e : ℕ)
    (hb : b < 2 ^ S.P.v) (hc : ¬ e < cut) (he : e - cut < S.P.T.l - cut) :
    cellEntry S Z cut N M η b e = OnBytes.Slice.ofF (η ⟨b, hb⟩ ⟨e - cut, he⟩) := by
  have h2 : b < 2 ^ S.P.v ∧ e - cut < S.P.T.l - cut := ⟨hb, he⟩
  unfold cellEntry cellEntryAt
  rw [if_neg hc, dif_pos h2]

end

/-! ## Row by row -/

section
variable {S : Sz} {Z : Sample GE S.En} {cut : ℕ} {N : MatrixNums} {sh : Shape}

/-- A row's message on the two sides: the same residues. -/
theorem message_agrees (h : Agree sh S cut) (M : Cells (S.toDecR Z cut) N)
    (tail pad : ℕ → ℕ → UInt64) (salt : ℕ → ByteArray) (b : ℕ) (hb : b < 2 ^ S.P.v) :
    (rowWords S (honestMsgs S (cellWords S Z cut N M fun b j => toF (pad b.val j.val))) b).map
        residue =
      (Bind.Twin.message sh (tableOf S Z cut N M tail pad salt) b).map residue := by
  have h1 := h.cut
  have h2 := h.l
  have hplain : sh.plain = cut := by
    show sh.l - 3 * sh.s = cut
    omega
  have hpads : sh.pads = S.P.T.l - cut := by
    show 3 * sh.s = S.P.T.l - cut
    omega
  rw [rowsResidues S _ b hb]
  unfold Bind.Twin.message
  rw [hplain, hpads]
  refine List.ext_getElem ?_ fun e g1 g2 => ?_
  · simp only [List.length_map, List.length_range, List.length_append]
    omega
  · have he : e < S.P.T.l := by
      simpa only [List.length_map, List.length_range] using g1
    simp only [List.getElem_map, List.getElem_range]
    rw [cellWords_getD S Z cut N M _ b e he, residue_residue]
    by_cases hc : e < cut
    · rw [List.getElem_append_left (by rw [List.length_map, List.length_range]; exact hc)]
      simp only [List.getElem_map, List.getElem_range]
      show residue (cellEntry S Z cut N M (fun b j => toF (pad b.val j.val)) b e) =
        residue (cellEntry S Z cut N M (fun _ _ => 0) b e)
      rw [cellEntry_before S Z cut N M _ (fun _ _ => 0) b e hc]
    · rw [List.getElem_append_right
        (by rw [List.length_map, List.length_range]; exact Nat.le_of_not_lt hc)]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [cellEntry_pad S Z cut N M _ b e hb hc (by omega)]
      show residue (OnBytes.Slice.ofF (OnBytes.Slice.toF (pad b (e - cut)))) =
        residue (pad b (e - cut))
      rw [ofF_toF, residue_residue]

/-- A row's tail on the two sides: the same residues. -/
theorem tail_agrees (h : Agree sh S cut) (M : Cells (S.toDecR Z cut) N)
    (tail pad : ℕ → ℕ → UInt64) (salt : ℕ → ByteArray) (b : ℕ) (hb : b < 2 ^ S.P.v) :
    (tailWords S (fun b q => toF (tail b.val q.val)) b).map residue =
      (Bind.Twin.tailOf sh (tableOf S Z cut N M tail pad salt) b).map residue := by
  unfold tailWords Bind.Twin.tailOf
  rw [dif_pos hb, h.r]
  refine List.ext_getElem ?_ fun q g1 g2 => ?_
  · simp only [List.length_map, List.length_ofFn, List.length_range]
  · simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range]
    show residue (OnBytes.Slice.ofF (OnBytes.Slice.toF (tail b q))) = residue (tail b q)
    rw [ofF_toF, residue_residue]

/-- **The column**: at every position the library's honest table has the position's number and the
running committer's column. -/
theorem columnAgrees (h : Agree sh S cut) : ColumnAgrees S Z cut N sh := by
  intro M tail pad salt x
  have hcode : sh.code = S.P.T := by
    show (⟨sh.a, sh.l, sh.r⟩ : Fmt.M1.Code) = S.P.T
    rw [h.a, h.l, h.r]
  have hrows : sh.rows = 2 ^ S.P.v := by
    show 2 ^ sh.v = 2 ^ S.P.v
    rw [h.v]
  refine Prod.ext rfl ?_
  show (List.range (2 ^ S.P.v)).map _ = ((List.range sh.rows).map _).map _
  rw [List.map_map, hrows, hcode]
  refine List.map_congr_left fun b hb => ?_
  exact symF_congr _ _ _ _ _ _ (message_agrees h M tail pad salt b (List.mem_range.1 hb))
    (tail_agrees h M tail pad salt b (List.mem_range.1 hb))

end

/-! ## What every column has -/

/-- Horner's value is below the prime. -/
theorem ok_hornerF (z : UInt64) : ∀ cs : List UInt64,
    Fmt.Fld.two.ok (Fmt.M1.hornerF z cs) = true
  | [] => (by decide : Fmt.Fld.two.ok 0 = true)
  | c :: cs => by
    show Fmt.Fld.two.ok (Fmt.Fld.two.add c (Fmt.Fld.two.mul z (Fmt.M1.hornerF z cs))) = true
    exact Fmt.Fld.ok_add _ _ _

/-- A symbol is below the prime, whatever the words. -/
theorem ok_symF (C : Fmt.M1.Code) (x : ℕ) (m rho : List UInt64) :
    Fmt.Fld.two.ok (Fmt.M1.symF C x m rho) = true :=
  ok_hornerF _ _

/-- Every word of the running committer's column is below the prime. -/
theorem ok_columnOf (sh : Shape) (rows : List (List UInt64 × List UInt64)) (x : ℕ) :
    ∀ w ∈ Bind.Twin.columnOf sh rows x, Fmt.Fld.two.ok w = true := by
  intro w hw
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hw
  exact ok_symF _ _ _ _

/-- The running committer's column has a word for each row. -/
theorem length_columnOf (sh : Shape) (T : Table) (x : ℕ) :
    (Bind.Twin.columnOf sh (Bind.Twin.laid sh T) x).length = 2 ^ sh.v := by
  unfold Bind.Twin.columnOf Bind.Twin.laid
  rw [List.length_map, List.length_map, List.length_range]
  rfl

/-- The encoder of the object over `codingCells` is the honest table: by unfolding. -/
theorem encIsHonestTab (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums) :
    EncIsHonestTab S Z cut N := by
  intro X pp req F P M r
  rfl

end Bind.Column

end

#print axioms Bind.Column.ofF_toF
#print axioms Bind.Column.rowsResidues
#print axioms Bind.Column.rowsBack
#print axioms Bind.Column.cellEntry_before
#print axioms Bind.Column.cellEntry_pad
#print axioms Bind.Column.message_agrees
#print axioms Bind.Column.tail_agrees
#print axioms Bind.Column.columnAgrees
#print axioms Bind.Column.ok_hornerF
#print axioms Bind.Column.ok_symF
#print axioms Bind.Column.ok_columnOf
#print axioms Bind.Column.length_columnOf
#print axioms Bind.Column.encIsHonestTab
