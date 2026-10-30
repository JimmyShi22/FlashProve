-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/OneCell.lean: adding 1 at the cell (0, 0) of the index changes one
coefficient of the committed table's rows' polynomials.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. It follows the honest committer's way from a matrix to the rows of a table,
and proves what adding 1 at one cell does there. No protocol occurs. The way
(Johnson/Flat/CodingCells.lean, OnBytes/Flat/CodingHonest.lean, OnBytes/Slice/Honest.lean): a matrix
and pads are written as words (cellWords), read as the rows' messages (honestMsgs), written as words
again (rowWords), and put with the tails' words into the rows' polynomials (honestPolys). A cell is
an element of the extension field GE; only its first coordinate over the base field GF is written
(cellEntry, Johnson/Flat/CodingCells.lean).
  rowPolys_bump   for every matrix M, pads η and tails' words tl, if 0 < cut, 0 < N.rows and
                  0 < S.P.T.l: rowPolys (bumpCell M) η tl = rowPolys M η tl + oneCoeff. Here
                  oneCoeff is 1 at the first coefficient of the message's part of row 0 (the
                  row "all false"), and 0 elsewhere (Johnson/LinkSim/AtText/TwoAnswers.lean).
  bumpCell_ne     if the matrix has a row, bumpCell M is another matrix than M.
This prepares a negative fact: two things differ.

How it fits. Johnson/LinkSim/AtHome/TwoIndices.lean uses bumpCell and rowPolys_bump to build two
indices that differ in one cell. That file, Johnson/LinkSim/AtHome/TwoPlains.lean and
Johnson/LinkSim/AtHome/TwoViews.lean use bumpCell_ne.

Other names (namespace OnBytes.LinkSim.AtText).
  bumpCell M      the matrix M with 1 added at the cell (0, 0).
  rowPolys M η tl the rows' polynomials of M, at the pads η and the tails' words tl.
  entry_bump      the word of entry e of row b, read in the field, changes by 1 at (0, 0) alone.
  rowPolys_msg, rowPolys_tail   a coefficient of the message's part; of the tail's part.

Notes.
- That M or bumpCell M is a model's matrix, or in any range, is not said (see
  Johnson/LinkSim/Spec.lean on the index).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.TwoAnswers
import Johnson.Flat.CodingCells

set_option autoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice OnBytes.Flat Cb Cb.Ood

variable (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)

/-- 1 added at the cell (0, 0). -/
def bumpCell (M : Cells (S.toDecR Z cut) N) : Cells (S.toDecR Z cut) N :=
  fun y c => if y.val = 0 ∧ c.val = 0 then M y c + 1 else M y c

/-- If the matrix has a row, adding 1 at the cell (0, 0) gives another matrix. -/
theorem bumpCell_ne (hr : 0 < N.rows) (M : Cells (S.toDecR Z cut) N) :
    bumpCell S Z cut N M ≠ M := by
  intro h
  have e := congrFun (congrFun h ⟨0, hr⟩) ⟨0, Nat.two_pow_pos _⟩
  unfold bumpCell at e
  rw [if_pos ⟨rfl, rfl⟩] at e
  exact one_ne_zero (add_eq_left.mp e)

/-- The rows' polynomials of a matrix. -/
def rowPolys (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (tl : ℕ → List UInt64) :
    S.ix.Row → S.Co → GE :=
  honestPolys S (rowWords S (honestMsgs S (cellWords S Z cut N M η))) tl

variable {S Z cut N}

/-- If 0 < cut and the matrix has a row, the word of entry e of row b, read in the field, changes
by 1 at (0, 0) and nowhere else. -/
theorem entry_bump (h0 : 0 < cut) (hr : 0 < N.rows) (M : Cells (S.toDecR Z cut) N)
    (η : PadsOf S cut) (b e : ℕ) :
    toF (cellEntry S Z cut N (bumpCell S Z cut N M) η b e) =
      toF (cellEntry S Z cut N M η b e) + if b = 0 ∧ e = 0 then 1 else 0 := by
  have hK : 0 < 2 ^ N.kLo := Nat.two_pow_pos _
  unfold cellEntry cellEntryAt
  by_cases he : e < cut
  · rw [if_pos he, if_pos he]
    by_cases h : e / 2 ^ N.kLo < N.rows ∧ b * 2 ^ N.kLo + e % 2 ^ N.kLo < 2 ^ (N.kLo + S.P.v)
    · rw [dif_pos h, dif_pos h, toF_ofF, toF_ofF]
      unfold bumpCell
      show (if e / 2 ^ N.kLo = 0 ∧ b * 2 ^ N.kLo + e % 2 ^ N.kLo = 0 then
        M ⟨_, h.1⟩ ⟨_, h.2⟩ + 1 else M ⟨_, h.1⟩ ⟨_, h.2⟩).c0 = (M ⟨_, h.1⟩ ⟨_, h.2⟩).c0 + _
      by_cases hz : e / 2 ^ N.kLo = 0 ∧ b * 2 ^ N.kLo + e % 2 ^ N.kLo = 0
      · have e1 : e < 2 ^ N.kLo := (Nat.div_eq_zero_iff_lt hK).1 hz.1
        have e2 : e % 2 ^ N.kLo = e := Nat.mod_eq_of_lt e1
        have e3 : e = 0 := by omega
        have e4 : b = 0 := by
          rcases Nat.eq_zero_or_pos b with hb | hb
          · exact hb
          · have := Nat.mul_pos hb hK
            omega
        rw [if_pos hz, if_pos ⟨e4, e3⟩]
        rfl
      · rw [if_neg hz, if_neg fun hbe : b = 0 ∧ e = 0 => hz (by
          rw [hbe.1, hbe.2]
          exact ⟨Nat.zero_div _, by rw [Nat.zero_mul, Nat.zero_mod]⟩), add_zero]
    · rw [dif_neg h, dif_neg h, if_neg fun hbe : b = 0 ∧ e = 0 => h (by
        rw [hbe.1, hbe.2, Nat.zero_div, Nat.zero_mul, Nat.zero_mod]
        exact ⟨hr, Nat.two_pow_pos _⟩), add_zero]
  · rw [if_neg he, if_neg he, if_neg fun hbe : b = 0 ∧ e = 0 => he (hbe.2 ▸ h0), add_zero]

theorem rowPolys_tail (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (tl : ℕ → List UInt64)
    (r : S.ix.Row) (k : S.Co) (hk : k.val < S.P.T.r) :
    rowPolys S Z cut N M η tl r k = algebraMap GF GE (toF ((tl (Sz.rowNo r)).getD k.val 0)) := by
  show algebraMap GF GE (if k.val < S.P.T.r then _ else _) = _
  rw [if_pos hk]

theorem rowPolys_msg (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (tl : ℕ → List UInt64)
    (r : S.ix.Row) (k : S.Co) (hk : S.P.T.r ≤ k.val) :
    rowPolys S Z cut N M η tl r k =
      algebraMap GF GE (toF (cellEntry S Z cut N M η (Sz.rowNo r) (k.val - S.P.T.r))) := by
  have hj : k.val - S.P.T.r < S.P.T.l := by
    have := k.isLt
    omega
  show algebraMap GF GE (if k.val < S.P.T.r then _ else
    toF ((rowWords S (honestMsgs S (cellWords S Z cut N M η)) (Sz.rowNo r)).getD
      (k.val - S.P.T.r) 0)) = _
  rw [if_neg (Nat.not_lt.2 hk),
    rowWords_getD S (honestMsgs S (cellWords S Z cut N M η)) r ⟨k.val - S.P.T.r, hj⟩, toF_ofF]
  show algebraMap GF GE (toF ((cellWords S Z cut N M η (Sz.rowNo r)).getD (k.val - S.P.T.r) 0)) = _
  rw [cellWords_getD S Z cut N M η _ _ hj]

/-- If 0 < cut, the matrix has a row and the message's part is not empty, adding 1 at the cell
(0, 0) adds 1 at the first coefficient of the message's part of row 0, and changes no other
coefficient. -/
theorem rowPolys_bump (h0 : 0 < cut) (hr : 0 < N.rows) (hl : 0 < S.P.T.l)
    (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (tl : ℕ → List UInt64) :
    rowPolys S Z cut N (bumpCell S Z cut N M) η tl =
      rowPolys S Z cut N M η tl +
        oneCoeff (fun _ => false) ⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ 1 := by
  funext r k
  show _ = rowPolys S Z cut N M η tl r k +
    (if r = (fun _ => false) then
      (Pi.single (⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ : S.Co) (1 : GE) : S.Co → GE)
      else 0) k
  by_cases hk : k.val < S.P.T.r
  · have hne : k ≠ (⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ : S.Co) := fun e => by
      have := congrArg Fin.val e
      simp only at this
      omega
    rw [rowPolys_tail _ _ _ _ _ hk, rowPolys_tail _ _ _ _ _ hk]
    split_ifs
    · rw [Pi.single_eq_of_ne hne, add_zero]
    · exact (add_zero _).symm
  · have hk' : S.P.T.r ≤ k.val := Nat.le_of_not_lt hk
    rw [rowPolys_msg _ _ _ _ _ hk', rowPolys_msg _ _ _ _ _ hk', entry_bump h0 hr, map_add]
    congr 1
    by_cases hr0 : r = fun _ => false
    · have e0 : Sz.rowNo r = 0 := by
        rw [hr0]
        exact Finset.sum_eq_zero fun t _ => if_neg Bool.false_ne_true
      rw [if_pos hr0, e0]
      by_cases hkk : k = (⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ : S.Co)
      · rw [hkk, Pi.single_eq_same, if_pos ⟨rfl, Nat.sub_self _⟩, map_one]
      · rw [Pi.single_eq_of_ne hkk, if_neg fun h => hkk (Fin.ext (by
          show k.val = S.P.T.r
          omega)), map_zero]
    · rw [if_neg hr0, if_neg fun h => hr0 (funext fun t => by
        rw [← testBit_rowNo r t, h.1]
        exact Nat.zero_testBit _), map_zero]
      rfl

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.bumpCell_ne
#print axioms OnBytes.LinkSim.AtText.entry_bump
#print axioms OnBytes.LinkSim.AtText.rowPolys_tail
#print axioms OnBytes.LinkSim.AtText.rowPolys_msg
#print axioms OnBytes.LinkSim.AtText.rowPolys_bump
