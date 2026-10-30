-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttLayNames.lean: for every late entry that the ledger of an attention sub-proof's
own rounds reads: in which matrix, which column and which rows its cells lie.

Cb/Pv/Att/End/Names.lean lists the names of the late entries, table by table.
Johnson/Road/Rows/AttLayRows.lean has the addresses of the cells under an entry of a table, by the
kind of the table. This file joins the two, at the sizes that the verifier's shape gives: for every
listed name (T, r), with x its place in the table (placeAtt), cell number k of the entry lies in the
table's matrix, in column x / n, at row (x % n) len + k, where len is the number of cells of an
entry and n the number of entries in a column, for the tables on ah, qa and ao. For the tables on as
the place numbers the columns of all parts: part x / (kAs / NAs), column x % (kAs / NAs), row k.

Main definitions: rowTabs, qaTabs, colTabs: the tables by kind and matrix (the table tO, on the
matrix ao, stands alone).
Main theorems.
 - names_row, names_qa, names_tO, names_col: the addresses, for every listed name and every k below
   len.
 - stretch_le: for n > 0 the rows of an entry lie below n len; that n > 0 at the shape's numbers is
   not shown, and stretch_le is applied to no table here.

What the theorems take as given: what the verifier's function shape tests or sets (L5.Norm, Sizes).
Positions are counted by the shape's number T.

What is not claimed. That the matrices have n len rows (for ah: wcH T; for qa and ao: wcQ T and wcO
T; for a part of as: 2^lmS): that is what the plan's record of the matrices says, and it is not read
here. That the verifier's list of tables has, for the table T, this matrix and this len. Nothing is
said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttLayRows
import Cb.Pv.Att.End.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Attention (Shape)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (AttTab namesOf of_mem_row of_mem_long of_mem_col)

/-- The tables on single features of the matrix ah. -/
def rowTabs : List AttTab := [.tMm, .tMd, .hW, .hX, .hE, .hT, .hPi, .hR2]

/-- The tables on blocks of features of the matrix qa. -/
def qaTabs : List AttTab := [.tQm, .tKm, .tQd, .tKd, .qO, .qVM, .qVD, .qF, .qKx]

/-- The tables on the matrix as. -/
def colTabs : List AttTab := [.tA, .tVM, .tVD]

/-- The rows of an entry lie inside a column of n stretches. -/
theorem stretch_le {n : ℕ} (hn : 0 < n) (x len : ℕ) : x % n * len + len ≤ n * len := by
  have h : x % n + 1 ≤ n := Nat.mod_lt x hn
  calc x % n * len + len = (x % n + 1) * len := by ring
    _ ≤ n * len := Nat.mul_le_mul_right _ h

variable (S : Shape)

/-- The tables on ah. -/
theorem names_row {T : AttTab} (hT : T ∈ rowTabs) {r : Raw}
    (h : r ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T) (k : ℕ) :
    L5.addrA S (r.atPos k) =
      (S.cf.NAs, placeAtt S T r % S.cf.wcH * S.T + k, placeAtt S T r / S.cf.wcH) := by
  have key : ∀ (n : ℕ) (mk : ℕ → ℕ → ℕ → Raw), (∀ a b c, IsRowName (mk a b c)) →
      r ∈ Cb.Pv.Att.End.rowNames (L5.dimOf S) n mk →
      L5.addrA S (r.atPos k) =
        (S.cf.NAs, placeRow S r % S.cf.wcH * S.T + k, placeRow S r / S.cf.wcH) := by
    intro n mk hmk hr
    obtain ⟨a, b, c, -, -, -, rfl⟩ := of_mem_row hr
    exact row_addr S _ (hmk a b c) k
  cases T with
  | tMm => exact key 4 (fun k b g => .mx k b g 0) (fun _ _ _ => trivial) h
  | tMd => exact key 4 (fun k b g => .mx k b g 0) (fun _ _ _ => trivial) h
  | hW => exact key 4 (fun k b g => .den k b g 0) (fun _ _ _ => trivial) h
  | hX => exact key _ (fun k b g => .ib k b g 0) (fun _ _ _ => trivial) h
  | hE => exact key 4 (fun k b g => .den k b g 0) (fun _ _ _ => trivial) h
  | hT => exact key 4 (fun k b g => .mx k b g 0) (fun _ _ _ => trivial) h
  | hPi => exact key _ (fun k b g => .ib k b g 0) (fun _ _ _ => trivial) h
  | hR2 => exact key _ (fun k b g => .ib k b g 0) (fun _ _ _ => trivial) h
  | tA => simp [rowTabs] at hT
  | tVM => simp [rowTabs] at hT
  | tVD => simp [rowTabs] at hT
  | tQm => simp [rowTabs] at hT
  | tKm => simp [rowTabs] at hT
  | tQd => simp [rowTabs] at hT
  | tKd => simp [rowTabs] at hT
  | tO => simp [rowTabs] at hT
  | qO => simp [rowTabs] at hT
  | qVM => simp [rowTabs] at hT
  | qVD => simp [rowTabs] at hT
  | qF => simp [rowTabs] at hT
  | qKx => simp [rowTabs] at hT

variable (N : L5.Norm S) (Z : Sizes S)
include N Z

/-- The tables on qa. -/
theorem names_qa {T : AttTab} (hT : T ∈ qaTabs) {r : Raw}
    (h : r ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T) {k : ℕ} (hk : k < 2 ^ S.ls * S.T) :
    L5.addrA S ((r.addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3, placeAtt S T r % (S.cf.wcQ / 2 ^ S.ls) * (2 ^ S.ls * S.T) + k,
        placeAtt S T r / (S.cf.wcQ / 2 ^ S.ls)) := by
  have Q : r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nb
      (fun k b g => .qry k b g 0 0) → L5.addrA S ((r.addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3, placeLong S r % (S.cf.wcQ / 2 ^ S.ls) * (2 ^ S.ls * S.T) + k,
        placeLong S r / (S.cf.wcQ / 2 ^ S.ls)) := by
    intro hr
    obtain ⟨l, b, g, ch, -, -, -, -, rfl⟩ := of_mem_long hr
    exact long_qry S N Z ch hk l b g
  have O : r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nb
      (fun k b g => .out k b g 0 0) → L5.addrA S ((r.addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3, placeLong S r % (S.cf.wcQ / 2 ^ S.ls) * (2 ^ S.ls * S.T) + k,
        placeLong S r / (S.cf.wcQ / 2 ^ S.ls)) := by
    intro hr
    obtain ⟨l, b, g, ch, -, -, -, -, rfl⟩ := of_mem_long hr
    exact long_out S N Z ch hk l b g
  have K : r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nl
      (fun k l g => .key k l g 0 0) → L5.addrA S ((r.addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3, placeLong S r % (S.cf.wcQ / 2 ^ S.ls) * (2 ^ S.ls * S.T) + k,
        placeLong S r / (S.cf.wcQ / 2 ^ S.ls)) := by
    intro hr
    obtain ⟨l, b, g, ch, -, -, -, -, rfl⟩ := of_mem_long hr
    exact long_key S N Z ch hk l b g
  have V : r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nl
      (fun k l g => .val k l g 0 0) → L5.addrA S ((r.addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3, placeLong S r % (S.cf.wcQ / 2 ^ S.ls) * (2 ^ S.ls * S.T) + k,
        placeLong S r / (S.cf.wcQ / 2 ^ S.ls)) := by
    intro hr
    obtain ⟨l, b, g, ch, -, -, -, -, rfl⟩ := of_mem_long hr
    exact long_val S N Z ch hk l b g
  cases T with
  | tQm => exact Q h
  | tQd => exact Q h
  | qF => exact Q h
  | qO => exact O h
  | tKm => exact K h
  | tKd => exact K h
  | qKx => exact K h
  | qVM => exact V h
  | qVD => exact V h
  | tA => simp [qaTabs] at hT
  | tVM => simp [qaTabs] at hT
  | tVD => simp [qaTabs] at hT
  | tMm => simp [qaTabs] at hT
  | tMd => simp [qaTabs] at hT
  | hW => simp [qaTabs] at hT
  | hX => simp [qaTabs] at hT
  | hE => simp [qaTabs] at hT
  | hT => simp [qaTabs] at hT
  | hPi => simp [qaTabs] at hT
  | hR2 => simp [qaTabs] at hT
  | tO => simp [qaTabs] at hT

/-- The table on ao. -/
theorem names_tO {r : Raw} (h : r ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS .tO) {k : ℕ}
    (hk : k < 2 ^ S.ls * S.T) :
    L5.addrA S ((r.addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 1, placeAtt S .tO r % (S.cf.wcO / 2 ^ S.ls) * (2 ^ S.ls * S.T) + k,
        placeAtt S .tO r / (S.cf.wcO / 2 ^ S.ls)) := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨l, b, g, ch, -, -, -, -, rfl⟩ := of_mem_long h
    exact long_qh S N Z ch hk b g
  · obtain ⟨l, b, g, ch, -, -, -, -, rfl⟩ := of_mem_long h
    exact long_qh' S N Z ch hk b g

/-- A plane below the diagonal holds whole columns of as. -/
theorem lmS_le_nM : S.cf.lmS ≤ S.nM := by
  have h := Z.lmS
  rw [N.nD] at h
  rw [N.nM]
  omega

/-- The tables on as. The place numbers the columns of all parts of as. -/
theorem names_col {T : AttTab} (hT : T ∈ colTabs) {r : Raw}
    (h : r ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T) {k : ℕ} (hk : k < 2 ^ S.cf.lmS) :
    L5.addrA S (r.addX k) =
      (placeAtt S T r / (S.kAs / S.cf.NAs), k, placeAtt S T r % (S.kAs / S.cf.NAs)) := by
  have kM : r ∈ Cb.Pv.Att.End.colNames (L5.dimOf S) S.cf.lmS .M → L5.addrA S (r.addX k) =
      (placeCol S r / (S.kAs / S.cf.NAs), k, placeCol S r % (S.kAs / S.cf.NAs)) := by
    intro hr
    obtain ⟨jj, b, hi, -, -, -, rfl⟩ := of_mem_col hr
    exact col_M S (lmS_le_nM S N Z) jj b hi hk
  have kD : r ∈ Cb.Pv.Att.End.colNames (L5.dimOf S) S.cf.lmS .D → L5.addrA S (r.addX k) =
      (placeCol S r / (S.kAs / S.cf.NAs), k, placeCol S r % (S.kAs / S.cf.NAs)) := by
    intro hr
    obtain ⟨jj, b, hi, -, -, -, rfl⟩ := of_mem_col hr
    exact col_D S (lmS_le_nM S N Z) Z.lmS jj b hi hk
  cases T with
  | tA =>
    rcases List.mem_append.mp h with h | h
    · exact kM h
    · exact kD h
  | tVM => exact kM h
  | tVD => exact kD h
  | tMm => simp [colTabs] at hT
  | tMd => simp [colTabs] at hT
  | hW => simp [colTabs] at hT
  | hX => simp [colTabs] at hT
  | hE => simp [colTabs] at hT
  | hT => simp [colTabs] at hT
  | hPi => simp [colTabs] at hT
  | hR2 => simp [colTabs] at hT
  | tQm => simp [colTabs] at hT
  | tKm => simp [colTabs] at hT
  | tQd => simp [colTabs] at hT
  | tKd => simp [colTabs] at hT
  | tO => simp [colTabs] at hT
  | qO => simp [colTabs] at hT
  | qVM => simp [colTabs] at hT
  | qVD => simp [colTabs] at hT
  | qF => simp [colTabs] at hT
  | qKx => simp [colTabs] at hT

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.names_row
#print axioms OnBytes.Road.Rows.names_qa
#print axioms OnBytes.Road.Rows.names_tO
#print axioms OnBytes.Road.Rows.names_col
