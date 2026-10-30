-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyReaders.lean: the committed matrix, the pads and the encoding randomness of a committed table
as three plain readers (number, number ↦ element of the base field), the rows of the table before
encoding laid out of them, and that these rows are the encoder's own. Definitions, statements and
proofs. General in the table's sizes.

Why. Whoever writes an honest prover's part reads the index and the committer's coins by row and
entry. The configuration of a committed table (`codingCells`, Johnson/Flat/CodingCells.lean;
E2E/TableMasked.lean) has them as functions on finite types. Here the two are tied, so that what a
part folds or sums is what the committer has encoded.

What is defined.
  `cellsReader M`, `padReader η`, `tailReader ρ`: the first coordinate of the cell in row y and
    column c; entry e of the pad of the table's row number b; entry t of that row's encoding
    randomness; 0 outside the shapes.
  `storedAt entry pad rows kLo cut l b e`: entry e of the message of the table's row number b: below
    rows · 2^kLo the matrix's entry in row e / 2^kLo and column e % 2^kLo + 2^kLo · b; from the cut
    up to l the pad; 0 between.
What is shown.
  **`stored_eq_cell`**: `storedAt` at the readers is the word that the encoder's message has there
    (`cellEntryAt`), read in the field; asked: the matrix's entries end before the cut.
  **`stored_eq_hold`**: so the message that holds M under the pads η (`honestMsgs` of `cellWords`),
    at the vertex of the bits of b, is `storedAt` at the readers, read in the extension field.
  `tail_eq`: the word that the encoder lays for a row's encoding randomness (`tailWords`) is
    `tailReader`'s value.

Limits. Readers and one layout. No fold, no oracle message, no coin is typed here. That another
text's layout of these rows is `storedAt` is not shown here. Nothing on hiding follows from this
file.


-/
import E2E.TableMasked
import E2E.TableStrong

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes.Flat (cellWords PadsOf MatrixNums Cells cellEntryAt tailWords)
open OnBytes.Slice (Sz GF GE toF ofF honestMsgs)

/-! ## 1. The readers -/

/-- The first coordinate of a cell; 0 outside the shape. -/
def cellsReader {rows cols : ℕ} (M : Fin rows → Fin cols → GE) (y c : ℕ) : GF :=
  if h : y < rows ∧ c < cols then (M ⟨y, h.1⟩ ⟨c, h.2⟩).c0 else 0

/-- A function on two finite ranges as a function of two numbers; 0 outside. -/
def gridReader {m n : ℕ} (η : Fin m → Fin n → GF) (b e : ℕ) : GF :=
  if h : b < m ∧ e < n then η ⟨b, h.1⟩ ⟨e, h.2⟩ else 0

/-- Entry e of the pad of the table's row number b. -/
abbrev padReader {S : Sz} {cut : ℕ} (η : PadsOf S cut) : ℕ → ℕ → GF := gridReader η

/-- Entry t of the encoding randomness of the table's row number b. -/
abbrev tailReader {S : Sz} (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) : ℕ → ℕ → GF := gridReader ρ

/-! ## 2. A row's message, out of the readers -/

/-- **Entry e of the message of the table's row number b.** -/
def storedAt (entry pad : ℕ → ℕ → GF) (rows kLo cut l b e : ℕ) : GF :=
  if e < rows * 2 ^ kLo then entry (e / 2 ^ kLo) (e % 2 ^ kLo + 2 ^ kLo * b)
  else if cut ≤ e ∧ e < l then pad b (e - cut) else 0

/-- **It is the encoder's word.** -/
theorem stored_eq_cell (rows kLo v cut l : ℕ) (M : Fin rows → Fin (2 ^ (kLo + v)) → GE)
    (η : Fin (2 ^ v) → Fin (l - cut) → GF) (hfit : rows * 2 ^ kLo ≤ cut) (b e : ℕ)
    (hb : b < 2 ^ v) (he : e < l) :
    storedAt (cellsReader M) (gridReader η) rows kLo cut l b e =
      toF (cellEntryAt rows kLo v cut l (fun y c => (M y c).c0) η b e) := by
  have hp : 0 < 2 ^ kLo := Nat.two_pow_pos kLo
  unfold storedAt cellEntryAt
  by_cases h1 : e < rows * 2 ^ kLo
  · have hy : e / 2 ^ kLo < rows := (Nat.div_lt_iff_lt_mul hp).2 h1
    have hm : e % 2 ^ kLo < 2 ^ kLo := Nat.mod_lt _ hp
    have hc : b * 2 ^ kLo + e % 2 ^ kLo < 2 ^ (kLo + v) := by
      rw [pow_add]
      calc b * 2 ^ kLo + e % 2 ^ kLo < b * 2 ^ kLo + 2 ^ kLo := Nat.add_lt_add_left hm _
        _ = (b + 1) * 2 ^ kLo := by ring
        _ ≤ 2 ^ v * 2 ^ kLo := Nat.mul_le_mul_right _ hb
        _ = 2 ^ kLo * 2 ^ v := Nat.mul_comm _ _
    have ec : e % 2 ^ kLo + 2 ^ kLo * b = b * 2 ^ kLo + e % 2 ^ kLo := by ring
    rw [if_pos h1, if_pos (lt_of_lt_of_le h1 hfit), dif_pos ⟨hy, hc⟩, OnBytes.Slice.toF_ofF]
    unfold cellsReader
    rw [dif_pos ⟨hy, ec ▸ hc⟩]
    exact congrArg (fun q => (M ⟨e / 2 ^ kLo, hy⟩ q).c0) (Fin.ext ec)
  · rw [if_neg h1]
    by_cases h2 : e < cut
    · have hy : ¬ (e / 2 ^ kLo < rows ∧ b * 2 ^ kLo + e % 2 ^ kLo < 2 ^ (kLo + v)) :=
        fun h => h1 ((Nat.div_lt_iff_lt_mul hp).1 h.1)
      rw [if_neg fun h => absurd h2 (Nat.not_lt.2 h.1), if_pos h2, dif_neg hy,
        OnBytes.Slice.toF_zero]
    · have h3 : b < 2 ^ v ∧ e - cut < l - cut := ⟨hb, by omega⟩
      rw [if_pos ⟨Nat.not_lt.1 h2, he⟩, if_neg h2, dif_pos h3, OnBytes.Slice.toF_ofF]
      unfold gridReader
      rw [dif_pos h3]

section
variable (S : Sz) (cut : ℕ) (N : MatrixNums) (Z : Cb.Ood.Sample GE S.En)

/-- **The message that holds M under the pads η is made of the readers' values.** -/
theorem stored_eq_hold (hfit : N.rows * 2 ^ N.kLo ≤ cut) (M : Cells (S.toDecR Z cut) N)
    (η : PadsOf S cut) (k : S.ix.Row) (j : S.En) :
    honestMsgs S (cellWords S Z cut N M η) (k, j) =
      algebraMap GF GE (storedAt (cellsReader M) (padReader η) N.rows N.kLo cut S.P.T.l
        (OnBytes.Slice.Sz.rowNo k) j.val) := by
  show algebraMap GF GE
    (toF ((cellWords S Z cut N M η (OnBytes.Slice.Sz.rowNo k)).getD j.val 0)) = _
  rw [OnBytes.Flat.cellWords_getD S Z cut N M η _ _ j.isLt,
    stored_eq_cell N.rows N.kLo S.P.v cut S.P.T.l M η hfit _ _ (OnBytes.Slice.rowNo_lt k) j.isLt]
  rfl

/-- **The word that the encoder lays for a row's encoding randomness is the reader's value**, at all
numbers. -/
theorem tail_eq (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) (b t : ℕ) :
    toF ((tailWords S ρ b).getD t 0) = tailReader ρ b t := by
  unfold tailWords
  show _ = gridReader ρ b t
  unfold gridReader
  by_cases hb : b < 2 ^ S.P.v
  · rw [dif_pos hb]
    by_cases ht : t < S.P.T.r
    · rw [dif_pos ⟨hb, ht⟩, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact ht),
        List.getElem_ofFn, OnBytes.Slice.toF_ofF]
    · rw [dif_neg fun h => ht h.2,
        List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact Nat.not_lt.1 ht),
        OnBytes.Slice.toF_zero]
  · rw [dif_neg hb, dif_neg fun h => hb h.1]
    exact OnBytes.Slice.toF_zero

end

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.stored_eq_cell
#print axioms AtPublicFiles.Key.stored_eq_hold
#print axioms AtPublicFiles.Key.tail_eq
