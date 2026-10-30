-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttLayRows.lean: which cells of the matrices of an attention sub-proof stand under
an entry of a table: the addresses, as equations on numbers.

An entry of a table of an attention sub-proof is a sum over a stretch of rows of one column of one
matrix. A late entry has a name: the table's name and the entry's first cell
(Cb/Pv/Att/End/Tabs.lean). Its place in the table is placeAtt (Johnson/Road/Rows/AttPortLate.lean).
The address of a cell, (matrix, row, column), is L5.addrA (Johnson/Road/Lane5AttDef.lean). This file
shows, for the three kinds of tables: with x the place of the name, len the number of rows of a
stretch and n the number of stretches in a column, cell number k of the entry has the address (the
table's matrix, row (x % n) len + k, column x / n).

Main theorems.
 - row_addr: tables on single features of the matrix ah (a stretch: the T positions of a feature).
 - long_addr: tables on blocks of features (a stretch: 2^ls features of T positions each).
   feat_addr: the reckoning. long_qry, long_out, long_key, long_val, long_qh, long_qh': for the six
   kinds of names.
 - col_addr: tables on the matrix as (a stretch: a whole column of a part of as; the place numbers
   the columns of all parts), for a plane whose first place is a multiple of a column's length.
   col_M, col_D: for the two regions.

What the theorems take as given: what the verifier's function shape tests or sets (L5.Norm, Sizes);
that the name's feature, or its entry of the region, is the first of its block.

What is not claimed. That the verifier's list of tables has, for each table, the matrix and the
length of a stretch that are named here: that is a fact on the run of its function tables. Nothing
is said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttPortLate
import Johnson.Road.Rows.AttLinMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (TenAt tenCell)
open OnBytes.Attention (Shape)
open Inst.Model.AttSeg (Raw)

/-! ## Tables on single features -/

/-- The names of the first cells of the entries of a table on ah. -/
def IsRowName : Raw → Prop
  | .mx _ _ _ _ => True
  | .den _ _ _ _ => True
  | .ib _ _ _ _ => True
  | _ => False

/-- A table on single features. Cell number k of the entry named r is the cell at position k. -/
theorem row_addr (S : Shape) (r : Raw) (hr : IsRowName r) (k : ℕ) :
    L5.addrA S (r.atPos k) =
      (S.cf.NAs, placeRow S r % S.cf.wcH * S.T + k, placeRow S r / S.cf.wcH) := by
  cases r with
  | mx _ _ _ _ => rfl
  | den _ _ _ _ => rfl
  | ib _ _ _ _ => rfl
  | c _ _ _ _ => exact hr.elim
  | qh _ _ _ _ => exact hr.elim
  | qh' _ _ _ _ => exact hr.elim
  | qry _ _ _ _ _ => exact hr.elim
  | out _ _ _ _ _ => exact hr.elim
  | key _ _ _ _ _ => exact hr.elim
  | val _ _ _ _ _ => exact hr.elim

/-! ## Tables on blocks of features -/

/-- The reckoning. φ: the first feature of a block of P features; wc: the features of a column,
whole blocks; k: the number of a cell in the block's stretch of P T rows. -/
theorem feat_addr (S : Shape) (a : ℕ) {P wc φ k : ℕ} (hP : 0 < P) (hw : P ∣ wc) (hφ : P ∣ φ)
    (hk : k < P * S.T) :
    L5.featCell S a wc (φ + k / S.T) (k % S.T) =
      (a, φ / P % (wc / P) * (P * S.T) + k, φ / P / (wc / P)) := by
  obtain ⟨w, rfl⟩ := hw
  obtain ⟨x, rfl⟩ := hφ
  have hc : k / S.T < P := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
  rw [Nat.mul_div_cancel_left _ hP, Nat.mul_div_cancel_left _ hP]
  unfold L5.featCell
  rw [Nat.mul_comm P x, block_mod hP w x _ hc, block_div hP w x _ hc]
  have e : (x % w * P + k / S.T) * S.T + k % S.T = x % w * (P * S.T) + k := by
    have h := Nat.div_add_mod' k S.T
    calc (x % w * P + k / S.T) * S.T + k % S.T
        = x % w * (P * S.T) + (k / S.T * S.T + k % S.T) := by ring
      _ = x % w * (P * S.T) + k := by rw [h]
  rw [e]

/-- The place of a block: the number of the block of its first feature. -/
theorem place_blk (S : Shape) (X : TenAt) (l lam hd ch : ℕ)
    (h : 2 ^ S.ls ∣ tenCell X l lam (hd * S.dh)) :
    placeTen S X l lam hd (0 + ch * 2 ^ S.ls) =
      (tenCell X l lam (hd * S.dh) + (0 + ch * 2 ^ S.ls)) / 2 ^ S.ls := by
  obtain ⟨x, hx⟩ := h
  unfold placeTen
  rw [hx, Nat.zero_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
    Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mul_comm (2 ^ S.ls) x, ← Nat.add_mul,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- A table on blocks of features, for a tensor X in matrix a with wc features a column. f: the
tensor's first feature for the name's limb, layer and head. -/
theorem long_addr (S : Shape) (a wc : ℕ) (hw : wc % 2 ^ S.ls = 0) (X : TenAt)
    (l lam hd ch k : ℕ) (h : 2 ^ S.ls ∣ tenCell X l lam (hd * S.dh)) (hk : k < 2 ^ S.ls * S.T) :
    L5.featCell S a wc (tenCell X l lam (hd * S.dh) + (0 + ch * 2 ^ S.ls + k / S.T)) (k % S.T) =
      (a, placeTen S X l lam hd (0 + ch * 2 ^ S.ls) % (wc / 2 ^ S.ls) * (2 ^ S.ls * S.T) + k,
        placeTen S X l lam hd (0 + ch * 2 ^ S.ls) / (wc / 2 ^ S.ls)) := by
  rw [place_blk S X l lam hd ch h, ← Nat.add_assoc]
  exact feat_addr S a (Nat.two_pow_pos _) (Nat.dvd_of_mod_eq_zero hw)
    (Nat.dvd_add h (by rw [Nat.zero_add]; exact Dvd.intro_left _ rfl)) hk

section Names
variable (S : Shape) (N : L5.Norm S) (Z : Sizes S) (ch : ℕ) {k : ℕ} (hk : k < 2 ^ S.ls * S.T)
include N Z hk

/-- The queries. -/
theorem long_qry (l b g : ℕ) :
    L5.addrA S ((((Raw.qry l b g 0 0).addN (ch * 2 ^ S.ls)).addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3,
        placeLong S ((Raw.qry l b g 0 0).addN (ch * 2 ^ S.ls)) % (S.cf.wcQ / 2 ^ S.ls) *
          (2 ^ S.ls * S.T) + k,
        placeLong S ((Raw.qry l b g 0 0).addN (ch * 2 ^ S.ls)) / (S.cf.wcQ / 2 ^ S.ls)) :=
  long_addr S _ _ Z.wcQ S.atQ l _ _ ch k (qa_aligned N Z l _ _).1 hk

/-- The outputs. -/
theorem long_out (l b g : ℕ) :
    L5.addrA S ((((Raw.out l b g 0 0).addN (ch * 2 ^ S.ls)).addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3,
        placeLong S ((Raw.out l b g 0 0).addN (ch * 2 ^ S.ls)) % (S.cf.wcQ / 2 ^ S.ls) *
          (2 ^ S.ls * S.T) + k,
        placeLong S ((Raw.out l b g 0 0).addN (ch * 2 ^ S.ls)) / (S.cf.wcQ / 2 ^ S.ls)) :=
  long_addr S _ _ Z.wcQ S.atO l _ _ ch k (qa_aligned N Z l _ _).2.2.2 hk

/-- The keys. -/
theorem long_key (l lam g : ℕ) :
    L5.addrA S ((((Raw.key l lam g 0 0).addN (ch * 2 ^ S.ls)).addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3,
        placeLong S ((Raw.key l lam g 0 0).addN (ch * 2 ^ S.ls)) % (S.cf.wcQ / 2 ^ S.ls) *
          (2 ^ S.ls * S.T) + k,
        placeLong S ((Raw.key l lam g 0 0).addN (ch * 2 ^ S.ls)) / (S.cf.wcQ / 2 ^ S.ls)) :=
  long_addr S _ _ Z.wcQ S.atK l lam g ch k (qa_aligned N Z l _ _).2.1 hk

/-- The values. -/
theorem long_val (l lam g : ℕ) :
    L5.addrA S ((((Raw.val l lam g 0 0).addN (ch * 2 ^ S.ls)).addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 3,
        placeLong S ((Raw.val l lam g 0 0).addN (ch * 2 ^ S.ls)) % (S.cf.wcQ / 2 ^ S.ls) *
          (2 ^ S.ls * S.T) + k,
        placeLong S ((Raw.val l lam g 0 0).addN (ch * 2 ^ S.ls)) / (S.cf.wcQ / 2 ^ S.ls)) :=
  long_addr S _ _ Z.wcQ S.atV l lam g ch k (qa_aligned N Z l _ _).2.2.1 hk

/-- The high parts of the first remainders. -/
theorem long_qh (b g : ℕ) :
    L5.addrA S ((((Raw.qh b g 0 0).addN (ch * 2 ^ S.ls)).addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 1,
        placeLong S ((Raw.qh b g 0 0).addN (ch * 2 ^ S.ls)) % (S.cf.wcO / 2 ^ S.ls) *
          (2 ^ S.ls * S.T) + k,
        placeLong S ((Raw.qh b g 0 0).addN (ch * 2 ^ S.ls)) / (S.cf.wcO / 2 ^ S.ls)) :=
  long_addr S _ _ Z.wcO (Attention.atRh S) 0 _ _ ch k (ao_aligned N Z 0 _ _).1 hk

/-- The high parts of the second remainders. -/
theorem long_qh' (b g : ℕ) :
    L5.addrA S ((((Raw.qh' b g 0 0).addN (ch * 2 ^ S.ls)).addN (k / S.T)).atPos (k % S.T)) =
      (S.cf.NAs + 1,
        placeLong S ((Raw.qh' b g 0 0).addN (ch * 2 ^ S.ls)) % (S.cf.wcO / 2 ^ S.ls) *
          (2 ^ S.ls * S.T) + k,
        placeLong S ((Raw.qh' b g 0 0).addN (ch * 2 ^ S.ls)) / (S.cf.wcO / 2 ^ S.ls)) :=
  long_addr S _ _ Z.wcO (Attention.atRhp S) 0 _ _ ch k (ao_aligned N Z 0 _ _).2 hk

end Names

/-! ## Tables on the matrix as -/

/-- A table on the matrix as. F: the first place of a plane, a multiple of the number of rows of a
column; hi: the number of a column within the plane; k: the row. The place numbers the columns of
all parts of as: kp columns a part. -/
theorem col_addr (S : Shape) {F : ℕ} (hF : 2 ^ S.cf.lmS ∣ F) (hi : ℕ) {k : ℕ}
    (hk : k < 2 ^ S.cf.lmS) :
    L5.asCell S (F + (0 + hi * 2 ^ S.cf.lmS + k)) =
      ((F >>> S.cf.lmS + (0 + hi * 2 ^ S.cf.lmS) / 2 ^ S.cf.lmS) / (S.kAs / S.cf.NAs), k,
        (F >>> S.cf.lmS + (0 + hi * 2 ^ S.cf.lmS) / 2 ^ S.cf.lmS) % (S.kAs / S.cf.NAs)) := by
  obtain ⟨x, rfl⟩ := hF
  have hP : 0 < 2 ^ S.cf.lmS := Nat.two_pow_pos _
  have e0 : 2 ^ S.cf.lmS * x + (0 + hi * 2 ^ S.cf.lmS + k) = (x + hi) * 2 ^ S.cf.lmS + k := by ring
  have e1 : ((x + hi) * 2 ^ S.cf.lmS + k) / 2 ^ S.cf.lmS = x + hi := by
    rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt hk, Nat.add_zero]
  have e2 : ((x + hi) * 2 ^ S.cf.lmS + k) % 2 ^ S.cf.lmS = k := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  unfold L5.asCell
  rw [e0, e1, e2, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ hP, Nat.zero_add,
    Nat.mul_div_cancel _ hP]

/-- The region below the diagonal. -/
theorem col_M (S : Shape) (hM : S.cf.lmS ≤ S.nM) (jj b hi : ℕ) {k : ℕ} (hk : k < 2 ^ S.cf.lmS) :
    L5.addrA S (((Raw.c .M jj b 0).addX (hi * 2 ^ S.cf.lmS)).addX k) =
      (placeCol S ((Raw.c .M jj b 0).addX (hi * 2 ^ S.cf.lmS)) / (S.kAs / S.cf.NAs), k,
        placeCol S ((Raw.c .M jj b 0).addX (hi * 2 ^ S.cf.lmS)) % (S.kAs / S.cf.NAs)) := by
  have eF : planeFirst S jj (b / S.HA) (b % S.HA) false =
      ((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nM := by
    unfold planeFirst
    rw [if_neg (by simp), if_neg (by simp), Nat.zero_add, Nat.shiftLeft_eq]
  have hF : 2 ^ S.cf.lmS ∣ planeFirst S jj (b / S.HA) (b % S.HA) false := by
    rw [eF]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hM) _
  show L5.asCell S (((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nM +
    (0 + hi * 2 ^ S.cf.lmS + k)) = _
  rw [← eF]
  exact col_addr S hF hi hk

/-- The region on the diagonal. -/
theorem col_D (S : Shape) (hM : S.cf.lmS ≤ S.nM) (hD : S.cf.lmS ≤ S.nD) (jj b hi : ℕ) {k : ℕ}
    (hk : k < 2 ^ S.cf.lmS) :
    L5.addrA S (((Raw.c .D jj b 0).addX (hi * 2 ^ S.cf.lmS)).addX k) =
      (placeCol S ((Raw.c .D jj b 0).addX (hi * 2 ^ S.cf.lmS)) / (S.kAs / S.cf.NAs), k,
        placeCol S ((Raw.c .D jj b 0).addX (hi * 2 ^ S.cf.lmS)) % (S.kAs / S.cf.NAs)) := by
  have eF : planeFirst S jj (b / S.HA) (b % S.HA) true =
      5 * S.Lam * S.HA * 2 ^ S.nM + ((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nD := by
    unfold planeFirst
    rw [if_pos rfl, if_pos rfl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hF : 2 ^ S.cf.lmS ∣ planeFirst S jj (b / S.HA) (b % S.HA) true := by
    rw [eF]
    exact Nat.dvd_add (Dvd.dvd.mul_left (pow_dvd_pow 2 hM) _)
      (Dvd.dvd.mul_left (pow_dvd_pow 2 hD) _)
  show L5.asCell S (5 * S.Lam * S.HA * 2 ^ S.nM +
    ((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nD + (0 + hi * 2 ^ S.cf.lmS + k)) = _
  rw [← eF]
  exact col_addr S hF hi hk

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.col_M
#print axioms OnBytes.Road.Rows.col_D
#print axioms OnBytes.Road.Rows.row_addr
#print axioms OnBytes.Road.Rows.long_qry
#print axioms OnBytes.Road.Rows.long_qh
#print axioms OnBytes.Road.Rows.col_addr
