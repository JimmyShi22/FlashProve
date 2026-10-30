-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/CellsInField.lean: A MATRIX OVER THE BASE FIELD, PADS AND TAILS OVER THE BASE
FIELD: THE LIBRARY'S TYPED ENCODER GIVES THE STAND-IN COMMITTER'S COLUMN. General in the sizes.
Definitions, statements and proofs.

Why. An honest prover that is written over typed values reads the index as a matrix over the base
field, by row and column, and the stored tables' pads and encoding randomness as field elements by
address. The stand-in committer (Johnson/Bind/Twin.lean) reads words. Johnson/Bind/Column.lean ties
the library's honest table to the stand-in committer's column at raw words, and
Johnson/Bind/Digits.lean spells the library's word of a cell at a matrix of integers. Here both are
taken at values in the field.

Main names (namespace `Bind.ForProver`).
  `cellsOfF`: a matrix over the base field, by plain numbers, as the library's matrix of cells.
  **`cellEntry_cellsOfF`**: the library's word at (table row b, place e), pads of 0, is the word of
    the matrix's element at (e / 2^kLo, b 2^kLo + e % 2^kLo), or 0 where the matrix has no such
    cell: if the matrix's cells fit a row's message before the pads (hfit).
  `wordsTable`: the stand-in committer's table of such a matrix, pads and tails: its plain entries
    are BY DEFINITION the library's own `cellEntry` at pads of 0; a pad or a tail's entry is the
    word below the prime that is read as it.
  `honestAt_wordsTable`: under `Bind.Column.Agree sh S cut`: at every position the library's honest
    table at these values has the position's number and the stand-in committer's column at
    `wordsTable`: `Bind.Column.columnAgrees` at one more matrix.
  `enc_wordsTable`: so has the encoder of the object over `codingCells`, at the pads and tails
    themselves, cut to the shape's addresses.
WHAT HOLDS THE PACKING. In the last two `cellEntry` stands on both sides: a fault in it would pass
them. What says where a matrix's element lies is `cellEntry_cellsOfF`, with `wordsTable_eq`
(Johnson/Bind/ForProver/LawsSizes.lean).

Limits. `Agree` and hfit are premises; Johnson/Bind/ColumnSizes.lean and
Johnson/Flat/ClaimsSizes.lean pay them at the two sizes that the library has. Where hfit fails
`cellEntry_cellsOfF` says nothing: the matrix's last rows then stand in no row of the table. No hash
function, no query and no salt is read: nothing on a hash tree, an out-of-domain sample or a
commitment ID. This file writes no honest prover. No binding of the commitment (the opening form),
no correctness of extraction, no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.Column
import Johnson.Bind.Digits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open Bind.Twin (Shape Table)
open Bind.Column (Agree honestAt tableOf columnAgrees encIsHonestTab ofF_zero)

section
variable (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)

/-- A matrix over the base field, by plain numbers, as the library's matrix of cells. Every cell
that it gives lies in the base field. The library's reader the other way (`AtPublicFiles.Key.cellsReader`,
E2E/KeyReaders.lean) keeps a cell's first coordinate alone: at a cell outside the base field two
coordinates are dropped in silence. -/
def cellsOfF (w : ℕ → ℕ → GF) : Cells (S.toDecR Z cut) N :=
  fun y c => algebraMap GF GE (w y.val c.val)

/-- **The library's word of a cell, at a matrix over the base field.** -/
theorem cellEntry_cellsOfF (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF) (b e : ℕ) :
    cellEntry S Z cut N (cellsOfF S Z cut N w) (fun _ _ => 0) b e =
      if e / 2 ^ N.kLo < N.rows ∧ b * 2 ^ N.kLo + e % 2 ^ N.kLo < 2 ^ (N.kLo + S.P.v) then
        OnBytes.Slice.ofF (w (e / 2 ^ N.kLo) (b * 2 ^ N.kLo + e % 2 ^ N.kLo))
      else 0 := by
  unfold cellEntry cellEntryAt
  by_cases hc : e < cut
  · rw [if_pos hc]
    by_cases hd : e / 2 ^ N.kLo < N.rows ∧ b * 2 ^ N.kLo + e % 2 ^ N.kLo < 2 ^ (N.kLo + S.P.v)
    · rw [dif_pos hd, if_pos hd]
      rfl
    · rw [dif_neg hd, if_neg hd]
  · have hr : ¬ e / 2 ^ N.kLo < N.rows := fun hlt =>
      hc (lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).1 hlt) hfit)
    rw [if_neg hc, if_neg fun hd => hr hd.1]
    split
    · exact ofF_zero
    · rfl

/-- The stand-in committer's table of a matrix, pads and tails over the base field: the plain
entries are the library's own words at pads of 0; a pad or a tail's entry is the word below the
prime that is read as it. The salts are a letter: no column reads them. -/
def wordsTable (w padF tailF : ℕ → ℕ → GF) (salt : ℕ → ByteArray) : Table :=
  tableOf S Z cut N (cellsOfF S Z cut N w) (fun b q => OnBytes.Slice.ofF (tailF b q))
    (fun b j => OnBytes.Slice.ofF (padF b j)) salt

end

section
variable {S : Sz} {Z : Sample GE S.En} {cut : ℕ} {N : MatrixNums} {sh : Shape}

/-- The library's honest table at values in the field has the stand-in committer's column. -/
theorem honestAt_wordsTable (h : Agree sh S cut) (w padF tailF : ℕ → ℕ → GF)
    (salt : ℕ → ByteArray) (x : S.Pos) :
    honestAt S Z cut N (cellsOfF S Z cut N w) (fun b q => OnBytes.Slice.ofF (tailF b q))
        (fun b j => OnBytes.Slice.ofF (padF b j)) x =
      (x.val, Bind.Twin.columnOf sh
        (Bind.Twin.laid sh (wordsTable S Z cut N w padF tailF salt)) x.val) :=
  columnAgrees h (cellsOfF S Z cut N w) _ _ salt x

/-- The typed encoder at the pads and tails themselves has the stand-in committer's column. -/
theorem enc_wordsTable (h : Agree sh S cut) (w padF tailF : ℕ → ℕ → GF) (salt : ℕ → ByteArray)
    (X : Type) (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Z cut) N pp req)
      (relationsAndEncodingOfClaims _ (codingCells S Z cut N pp req)))) (P : F.Provers) (x : S.Pos) :
    (F.withProvers P).encodeIndex (cellsOfF S Z cut N w)
        (fun b j => padF b.val j.val, fun b q => tailF b.val q.val) x =
      (x.val, Bind.Twin.columnOf sh
        (Bind.Twin.laid sh (wordsTable S Z cut N w padF tailF salt)) x.val) := by
  rw [← honestAt_wordsTable h w padF tailF salt x, encIsHonestTab S Z cut N X pp req F P]
  unfold honestAt
  simp only [OnBytes.Slice.toF_ofF]

end

end Bind.ForProver

end

#print axioms Bind.ForProver.cellEntry_cellsOfF
#print axioms Bind.ForProver.honestAt_wordsTable
#print axioms Bind.ForProver.enc_wordsTable
#print axioms Bind.ForProver.cellsOfF
#print axioms Bind.ForProver.wordsTable
