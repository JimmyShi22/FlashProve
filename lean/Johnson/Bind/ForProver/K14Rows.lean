-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/K14Rows.lean: TWO TEXTS OF A COMMITTED TABLE'S ROWS ARE ONE, WHERE THE TEST
`rowsFit` PASSES, AT THE ROWS BELOW 2^v: the rows that the honest side of the linear claim's shared
rounds (the shared chain) folds (`ProofFile.Honest.K14.entriesOf`, `rowsOf`,
Johnson/Desc/ProofFile/Honest/K14/Parts.lean) and the rows that the encoded index for an honest
prover encodes (`rowMsgF`, `rowTailF` over `entryAtF`, Johnson/Bind/ForProver/Rows.lean).
Definitions, statements and proofs.

Why. The shared rounds' honest side sends a fold of the committed table's rows before encoding; a
run reads columns of the same table after encoding. The first text packs the matrix of digits into
rows by itself; the second is tied to the message and tail of the stand-in committer on byte strings
(`Bind.Twin.commitW`, Johnson/Bind/Twin.lean) in Johnson/Bind/ForProver/Laws.lean and
Johnson/Bind/ForProver/JoinsK14.lean. If the two parted, the folded row would not be the fold of the
rows that are encoded and committed.

Main names (namespace `Bind.ForProver`).
  `rowLaidE S w ρ r k`: row r at the place k, laid out as the folded row is: the message (`rowMsgF`)
    below ell, the tail (`rowTailF`) from `tailFirst` on, as the programs' elements.
  `rowsFit_of_ok`: the library's own test on the shape (`OnBytes.Params.LinShape.ok`,
    OnBytes/Iop/Lin.lean) gives the test `rowsFit`.
  `eOfF_zero`, `rowsFit_spec`, `ell_le_tailFirst`: the field's 0 is the programs' zero; what the
    test says; the folded tail begins at or behind the message's end.
  `toF_entryAtF`: at a row below 2^v the packing's word, read in the field, is the matrix's element
    at (k / 2^kLo, k % 2^kLo + 2^kLo r) where k is below rows 2^kLo, and 0 elsewhere.
  **`entriesOf_eq`**: at every row below 2^v and every place: `entriesOf` is the packing's word.
  **`rowsOf_eq`**: where `rowsFit` passes, at every row below 2^v and every place: `rowsOf` at the
    pads and tails of ρ is `rowLaidE`.

Limits. THE TWO PREMISES ARE NOT IDLE: so the two texts read. Of `rowsFit` an example in Lean shows
it (`parts_at_pads`, `parts_example`, Johnson/Bind/ForProver/JoinsK14.lean); of the bound on the row
none. From the row 2^v on `entryAtF` gives 0 and `entriesOf` reads the reader at a column that the
matrix has not. Where the matrix's rows have no room before the pads (`rowsFit`'s second clause
fails) `rowsOf` lays the matrix's element at places where the stand-in committer lays a pad, and
from ell on, as far as the matrix reaches, where the committed row has nothing or its tail: there it
is the text of other rows than those that are encoded and committed. Of `rowsFit`'s two clauses the
second alone is used. Nothing on the encoder: that a column's symbol is the value of the polynomial
with these coefficients is said in Johnson/Bind/ForProver/Laws.lean. Nothing on a fold, on the
folded row's own pads, tails or masks, or on the law of any coin. One committed table; which of the
protocol's tables it is, the first or a copy, is not said here. No completeness, no index privacy;
nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Enc
import Johnson.Desc.ProofFile.Honest.K14.Parts
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E zeroE)
open OnBytes.Params (LinShape FoldeqShape)
open OnBytes.Slice (toF ofF toF_ofF)
open ProofFile.Honest (TableRand Weights eOfF)

/-- **Row r of a committed table before encoding, at the place k**, laid out as the folded row is:
the message, pads among it, below ell; the random tail from `tailFirst` on; the programs' zero
elsewhere. -/
def rowLaidE (S : LinShape) (w : Weights) (ρ : TableRand) (r k : ℕ) : E :=
  if k < S.fold.index.code.ell then
    eOfF (rowMsgF (shapeOfIndex S.fold.index)
      (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ r k)
  else if S.fold.tailFirst ≤ k ∧ k < S.fold.entries then
    eOfF (rowTailF ρ r (k - S.fold.tailFirst))
  else zeroE

/-- The field's 0 is the programs' zero. -/
theorem eOfF_zero : eOfF 0 = zeroE := by
  unfold eOfF ofF
  rw [ZMod.val_zero]
  rfl

/-- What the test with code says. -/
theorem rowsFit_spec {S : LinShape}
    (h : rowsFit (shapeOfIndex S.fold.index) S.kLo S.matrixRows = true) :
    3 * S.fold.index.answers ≤ S.fold.index.code.ell ∧
      S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain := by
  unfold rowsFit at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact h

/-- **The library's own test on the shape gives the test `rowsFit`.** -/
theorem rowsFit_of_ok (S : LinShape) (h : S.ok = true) :
    rowsFit (shapeOfIndex S.fold.index) S.kLo S.matrixRows = true := by
  simp only [OnBytes.Params.LinShape.ok, OnBytes.Params.FoldeqShape.ok,
    OnBytes.Params.IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : S.fold.index.pads < S.fold.index.code.ell := h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  have h2 : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain := h.1.1.1.1.1.1.1.1.1.2
  have h3 : 3 * S.fold.index.answers ≤ S.fold.index.code.ell := Nat.le_of_lt h1
  unfold rowsFit
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨h3, h2⟩

/-- The folded tail begins at or behind the message's end. -/
theorem ell_le_tailFirst (S : FoldeqShape) : S.index.code.ell ≤ S.tailFirst := by
  have hs : 0 < 2 ^ S.index.code.logR := Nat.two_pow_pos _
  have hd := Nat.div_add_mod (S.index.code.ell + 2 ^ S.index.code.logR - 1)
    (2 ^ S.index.code.logR)
  have hm := Nat.mod_lt (S.index.code.ell + 2 ^ S.index.code.logR - 1) hs
  show S.index.code.ell ≤
    (S.index.code.ell + 2 ^ S.index.code.logR - 1) / 2 ^ S.index.code.logR *
      2 ^ S.index.code.logR
  rw [Nat.mul_comm]
  omega

/-- **The packing's word, read in the field**, at a row that the table has. -/
theorem toF_entryAtF (kLo rows v : ℕ) (w : ℕ → ℕ → Cb.Gl.F) (r k : ℕ) (hr : r < 2 ^ v) :
    toF (entryAtF kLo rows v w r k) =
      if k < rows * 2 ^ kLo then w (k / 2 ^ kLo) (k % 2 ^ kLo + 2 ^ kLo * r) else 0 := by
  have hK : 0 < 2 ^ kLo := Nat.two_pow_pos _
  unfold entryAtF
  by_cases hk : k < rows * 2 ^ kLo
  · have h1 : k / 2 ^ kLo < rows := (Nat.div_lt_iff_lt_mul hK).2 hk
    have hm : k % 2 ^ kLo < 2 ^ kLo := Nat.mod_lt _ hK
    have h3 : (r + 1) * 2 ^ kLo ≤ 2 ^ v * 2 ^ kLo := Nat.mul_le_mul_right _ hr
    have h2 : r * 2 ^ kLo + k % 2 ^ kLo < 2 ^ (kLo + v) := by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ kLo) (2 ^ v)]
      rw [Nat.add_mul, Nat.one_mul] at h3
      omega
    rw [if_pos ⟨h1, h2⟩, if_pos hk, toF_ofF, Nat.add_comm, Nat.mul_comm]
  · have h1 : ¬ (k / 2 ^ kLo < rows ∧ r * 2 ^ kLo + k % 2 ^ kLo < 2 ^ (kLo + v)) :=
      fun h => hk ((Nat.div_lt_iff_lt_mul hK).1 h.1)
    rw [if_neg h1, if_neg hk]
    exact OnBytes.Slice.toF_zero

/-- **The places that hold the matrix**: the two texts are one, at every row that the table has. -/
theorem entriesOf_eq (S : LinShape) (w : Weights) (r k : ℕ) (hr : r < 2 ^ S.fold.index.v) :
    ProofFile.Honest.K14.entriesOf S w r k =
      eOfF (toF (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry r k)) := by
  rw [toF_entryAtF S.kLo S.matrixRows S.fold.index.v w.entry r k hr]
  unfold ProofFile.Honest.K14.entriesOf
  by_cases hk : k < S.matrixRows * 2 ^ S.kLo
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    exact eOfF_zero.symm

/-- **The rows, whole**: the two texts are one, where the matrix fits before the pads, at every row
that the table has and every place. -/
theorem rowsOf_eq (S : LinShape) (w : Weights) (ρ : TableRand)
    (hfit : rowsFit (shapeOfIndex S.fold.index) S.kLo S.matrixRows = true) (r k : ℕ)
    (hr : r < 2 ^ S.fold.index.v) :
    ProofFile.Honest.K14.rowsOf S w ⟨ρ.pad, ρ.tail⟩ r k = rowLaidE S w ρ r k := by
  obtain ⟨-, h4⟩ := rowsFit_spec hfit
  have hpl : S.fold.index.plain ≤ S.fold.index.code.ell := Nat.sub_le _ _
  have htf : S.fold.index.code.ell ≤ S.fold.tailFirst := ell_le_tailFirst S.fold
  unfold ProofFile.Honest.K14.rowsOf rowLaidE rowMsgF rowTailF
  by_cases h1 : k < S.matrixRows * 2 ^ S.kLo
  · have h2 : k < (shapeOfIndex S.fold.index).plain := lt_of_lt_of_le h1 h4
    have h5 : k < S.fold.index.code.ell := lt_of_lt_of_le (lt_of_lt_of_le h1 h4) hpl
    rw [if_pos h1, if_pos h5, if_pos h2]
    exact entriesOf_eq S w r k hr
  · rw [if_neg h1]
    by_cases h5 : k < S.fold.index.code.ell
    · rw [if_pos h5]
      by_cases h2 : k < S.fold.index.plain
      · have h2' : k < (shapeOfIndex S.fold.index).plain := h2
        have n2 : ¬ (S.fold.index.plain ≤ k ∧ k < S.fold.index.code.ell) :=
          fun h => Nat.not_lt.2 h.1 h2
        have n3 : ¬ (S.fold.tailFirst ≤ k ∧ k < S.fold.entries) :=
          fun h => Nat.not_lt.2 (Nat.le_trans htf h.1) h5
        rw [if_neg n2, if_neg n3, if_pos h2',
          toF_entryAtF S.kLo S.matrixRows S.fold.index.v w.entry r k hr, if_neg h1]
        exact eOfF_zero.symm
      · have h2' : ¬ k < (shapeOfIndex S.fold.index).plain := h2
        have h5' : k < (shapeOfIndex S.fold.index).l := h5
        rw [if_pos ⟨Nat.not_lt.1 h2, h5⟩, if_neg h2', if_pos h5']
        rfl
    · have n2 : ¬ (S.fold.index.plain ≤ k ∧ k < S.fold.index.code.ell) := fun h => h5 h.2
      rw [if_neg n2, if_neg h5]

end Bind.ForProver

#print axioms Bind.ForProver.eOfF_zero
#print axioms Bind.ForProver.rowsFit_spec
#print axioms Bind.ForProver.rowsFit_of_ok
#print axioms Bind.ForProver.ell_le_tailFirst
#print axioms Bind.ForProver.toF_entryAtF
#print axioms Bind.ForProver.entriesOf_eq
#print axioms Bind.ForProver.rowsOf_eq
#print axioms Bind.ForProver.rowLaidE
