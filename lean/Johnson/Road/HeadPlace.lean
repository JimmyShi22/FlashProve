-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadPlace.lean: where a cell stands in the matrices of the output head's sub-proof: the
verifier's rule against the library's places.

The verifier's claims on the head never read a cell. They read entries of tables, and an entry
stands for a run of rows of one column of one matrix of the sub-proof's list (hf in several parts,
hd, hr, bH, and the residual stream, which the last group of layers commits to). The forms name an
entry by a feature's number, or by the number of a block of features. That fixes a rule: feature φ
at position i stands in row (φ mod fc) T + i of column φ / fc, counted across the parts of its
matrix, where a column holds fc features. The library has its own rule (Head.rowOf, Head.colOf in
Inst/Model/Head/Index.lean), and puts all matrices of a segment one below the other, in slots of
2^16 rows of one matrix (Name.place, ownX in Cm/SegLayout.lean). This file shows that, at the sizes
for which the library's head is written, the two rules give one place.

Main definitions.
 - placeIn, cellIn: the verifier's rule, with the sizes as letters.
 - cellsH: the library's record of the head's cells (Inst.Model.Head.Cells), read in the entries of
   the matrices of the sub-proof's list by that rule.
 - FullH: the nine public numbers of the head at which the library's head is written.
 - LaidH, NumH, BorderH: the sizes of the matrices, in the layout's words and as numerals.
 - slotNo, stackedH: the dictionary. From the lists of matrices of the sub-proofs it makes the
   library's family of matrices, one for each segment: which slot is which matrix of which list.
 - LentH: the matrix that the head borrows has the entries of the lender's matrix.

What is compared with what.
 - laidH_of_layout, numH_of_layout: the verifier's layout with itself, then with numerals.
 - borderH_of_layout: the verifier's record of the stream's matrix with numerals, through the
   library's sizes of a feed-forward segment.
 - placeIn_hf, placeIn_hd, placeIn_hr, placeIn_x: the verifier's rule with the library's rowOf and
   colOf.
 - stacked_hf, stacked_hd, stacked_hr, stacked_x: cellsH with the library's Name.place and ownX,
   read in stackedH.
 - lender_x, one_cell_x: the head's cell of the stream with the cell x8 of the last feed-forward
   segment, as Johnson/Road/FormsKeysAddr.lean reads it in the lender's own list.
 - readsAt_cellsH, readsAtMain_cellsH, tH_cellsH: the same in the library's own records: ReadsAt
   (Cm/SegHead.lean), ReadsAtMain (Policy/Seg/Dict.lean), tH (Cm/TargetSegHead.lean).

The hypotheses, and where they are met.
 - FullH h: nine equations on public numbers. The parameter file of the full-size example
   (prover/examples/target_full_f2) has these numbers (a run: Johnson/Road/HeadPlaceRun.lean).
 - layout returns: at that example, by the same run.
 - Switches, Sized, Sized2 at the library's reference sizes: theorems at the shape of that example
   (switchesK, sizedKF in Johnson/Road/FormsKeysRunK.lean).
 - LentH: no theorem concludes it. The verifier compares the two plans' records of the matrix and
   reads the lender's commitment; that this makes the entries equal is not looked at here.

What is not claimed. cellsH is a definition of this file. It takes the library's number of a feature
as the verifier's. That a tensor of hf begins at the feature at which the library has it is not
shown here: it stands in the record Laid of Johnson/Road/HeadLines.lean; for the stream alone it is
a theorem of this file (borderH_of_layout). So this file holds matrix, part, column and row of a
feature, not which feature a value's limb is. That the verifier's tables of reads follow the rule of
cellsH is the matter of Johnson/Road/HeadReads.lean; a run over all entries of all tables is in
Johnson/Road/HeadPlaceRun.lean. The entries of the matrices are any functions: nothing ties them to
a commitment. Nothing is said of bH, which holds no cell, of the attention segments' matrices, or of
any slot of a feed-forward segment but the one that the head reads. At other sizes the library has
no head on cells, and nothing is said. Nothing here is a statement on what a verifier's acceptance
shows. The program does not import this file.
-/
import Johnson.Road.FormsKeysAddr
import OnBytes.Model.VerifyPublic
import Cm.SegLayoutProofs
import Cm.TargetSegHead
import Policy.Seg.Dict

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (roundUp exc ledNRH tenCell)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL Border)
open OnBytes.Model.Verify (borderOf)
open Inst.Model.All (DF nGr)
open Inst.Model.Head (rowOf colOf perCol nFeat nT)
open Cm.Seg (Name ownX stack colsHead colsFF)

/-! ## The verifier's rule -/

/-- The part, the row and the column of the cell of feature φ at position i, in a matrix whose parts
have k columns, whose columns hold fc features, at T positions. -/
def placeIn (k fc T φ i : ℕ) : ℕ × ℕ × ℕ := (φ / fc / k, φ % fc * T + i, φ / fc % k)

/-- The cell of feature φ at position i of a matrix whose first part has the number first in the
list of matrices M. -/
def cellIn {K : Type} (M : Mats K) (first k fc T φ i : ℕ) : K :=
  M (first + φ / fc / k) (φ % fc * T + i) (φ / fc % k)

/-- cellIn reads the entry at placeIn. -/
theorem cellIn_place {K : Type} (M : Mats K) (first k fc T φ i : ℕ) :
    cellIn M first k fc T φ i =
      M (first + (placeIn k fc T φ i).1) (placeIn k fc T φ i).2.1 (placeIn k fc T φ i).2.2 := rfl

/-- The head's cells, read in the entries M of the matrices of the sub-proof's list. The list has
the parts of hf, then hd, hr, bH and the stream (matsH in OnBytes/Model/HeadPlan.lean). Feature φ of
the stream, in the library's count, is limb φ / d of channel φ mod d; the verifier's record b of the
stream's matrix says which feature of the matrix that is. -/
def cellsH {K : Type} (h : Model.Head.Shape) (L : HL) (b : Border) (M : Mats K) :
    Inst.Model.Head.Cells K where
  hf φ i := cellIn M 0 L.k (L.m / h.T) h.T φ i
  hd φ i := cellIn M h.NHf L.kD (L.mD / h.T) h.T φ i
  hr φ i := cellIn M (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i
  x φ i := cellIn M (h.NHf + 3) b.kxb (b.mxb / h.T) h.T (b.cell (φ / h.d) (φ % h.d)) i

/-- Cells read in the images of the entries are the images of the cells. -/
theorem cellsH_map {K K' : Type} (f : K → K') (h : Model.Head.Shape) (L : HL) (b : Border)
    (M : Mats K) : cellsH h L b (fun a r c => f (M a r c)) = (cellsH h L b M).map f := rfl

/-! ## The sizes of the head's matrices -/

/-- The public numbers of the head at which the library's head is written. -/
structure FullH (h : Model.Head.Shape) : Prop where
  /-- the logarithm of the number of positions -/
  lt : h.lt = 10
  /-- the logarithm of the rows of a block -/
  la : h.la = 16
  /-- the model's width -/
  d : h.d = 5120
  /-- the vocabulary -/
  V : h.V = 202048
  /-- the limbs of a value of the stream -/
  XL : h.XL = 5
  /-- the logarithm of the rows of a part of hf -/
  lmhf : h.lmhf = 16
  /-- the parts of hf -/
  NHf : h.NHf = 4
  /-- the logarithm of the rows of hd -/
  lmhd : h.lmhd = 14
  /-- the logarithm of the rows of hr -/
  lmhr : h.lmhr = 13

/-- The sizes of hf, hd and hr, in the words of numbers (OnBytes/Model/HeadLayout.lean). -/
structure LaidH (h : Model.Head.Shape) (L : HL) : Prop where
  /-- the rows of a part of hf -/
  m : L.m = 2 ^ h.lmhf
  /-- the columns of a part of hf -/
  k : L.k = roundUp (4 * h.d + (3 + exc) * roundUp h.V h.S2) (h.NHf * (2 ^ h.lmhf / h.T)) /
    (h.NHf * (2 ^ h.lmhf / h.T))
  /-- the rows of hd -/
  mD : L.mD = 2 ^ h.lmhd
  /-- the columns of hd -/
  kD : L.kD = roundUp (2 * h.d) (2 ^ h.lmhd / h.T) / (2 ^ h.lmhd / h.T)
  /-- the rows of hr -/
  mR : L.mR = 2 ^ h.lmhr
  /-- the columns of hr -/
  kR : L.kR = roundUp (ledNRH h.XL) (2 ^ h.lmhr / h.T) / (2 ^ h.lmhr / h.T)

/-- The numbers that numbers returns. -/
theorem laidH_of_numbers {h : Model.Head.Shape} {L : HL} (hL : Model.Head.numbers h = .ok L) :
    LaidH h L := by
  unfold Model.Head.numbers at hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  cases hL
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every layout of the head that the verifier returns has these sizes: what follows numbers in
layout changes other fields. -/
theorem laidH_of_layout {h : Model.Head.Shape} {tau : Array F} {L : HL}
    (hL : Model.Head.layout h tau = .ok L) : LaidH h L := by
  unfold Model.Head.layout at hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨L0, h0, hL⟩ := ok_of_bind hL
  obtain ⟨calls, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨fs, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨kb, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨pub, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  obtain ⟨-, -, hL⟩ := ok_of_bind hL
  have e := (Except.ok.inj hL).symm
  subst e
  have A := laidH_of_numbers h0
  exact ⟨A.m, A.k, A.mD, A.kD, A.mR, A.kR⟩

/-- The sizes as numerals. -/
structure NumH (h : Model.Head.Shape) (L : HL) : Prop where
  /-- the positions -/
  T : h.T = 1024
  /-- the parts of hf -/
  NHf : h.NHf = 4
  /-- the model's width -/
  d : h.d = 5120
  /-- hf: the rows and the columns of a part, the features of a column -/
  m : L.m = 65536
  k : L.k = 4816
  fc : L.m / h.T = 64
  /-- hd -/
  mD : L.mD = 16384
  kD : L.kD = 640
  fcD : L.mD / h.T = 16
  /-- hr -/
  mR : L.mR = 8192
  kR : L.kR = 15
  fcR : L.mR / h.T = 8

/-- Two to a number that is known. -/
theorem pow_known {l a n : ℕ} (hl : l = a) (hn : 2 ^ a = n) : 2 ^ l = n := by
  subst hl
  exact hn

/-- A quotient of two numbers that are known. -/
theorem div_known {x y a b n : ℕ} (hx : x = a) (hy : y = b) (hn : a / b = n) : x / y = n := by
  subst hx hy
  exact hn

/-- A difference of two numbers that are known. -/
theorem sub_known {x y a b n : ℕ} (hx : x = a) (hy : y = b) (hn : a - b = n) : x - y = n := by
  subst hx hy
  exact hn

/-- The columns of a part of hf at the full size. -/
theorem k_known {d V S N l T : ℕ} (hd : d = 5120) (hV : V = 202048) (hS : S = 64) (hN : N = 4)
    (hl : l = 16) (hT : T = 1024) :
    roundUp (4 * d + (3 + exc) * roundUp V S) (N * (2 ^ l / T)) / (N * (2 ^ l / T)) = 4816 := by
  subst hd hV hS hN hl hT
  decide

/-- The columns of hd at the full size. -/
theorem kD_known {d l T : ℕ} (hd : d = 5120) (hl : l = 14) (hT : T = 1024) :
    roundUp (2 * d) (2 ^ l / T) / (2 ^ l / T) = 640 := by
  subst hd hl hT
  decide

/-- The columns of hr at the full size. -/
theorem kR_known {X l T : ℕ} (hX : X = 5) (hl : l = 13) (hT : T = 1024) :
    roundUp (ledNRH X) (2 ^ l / T) / (2 ^ l / T) = 15 := by
  subst hX hl hT
  decide

/-- At the full size the sizes are these numerals. -/
theorem numH_of_laid {h : Model.Head.Shape} {L : HL} (hF : FullH h) (A : LaidH h L) : NumH h L := by
  have hT : h.T = 1024 := pow_known hF.lt (by decide)
  have hS : h.S2 = 64 :=
    pow_known (a := 6) (sub_known hF.la hF.lt (by decide)) (by decide)
  have hm : L.m = 65536 := A.m.trans (pow_known hF.lmhf (by decide))
  have hmD : L.mD = 16384 := A.mD.trans (pow_known hF.lmhd (by decide))
  have hmR : L.mR = 8192 := A.mR.trans (pow_known hF.lmhr (by decide))
  exact {
    T := hT
    NHf := hF.NHf
    d := hF.d
    m := hm
    k := A.k.trans (k_known hF.d hF.V hS hF.NHf hF.lmhf hT)
    fc := div_known hm hT (by decide)
    mD := hmD
    kD := A.kD.trans (kD_known hF.d hF.lmhd hT)
    fcD := div_known hmD hT (by decide)
    mR := hmR
    kR := A.kR.trans (kR_known hF.XL hF.lmhr hT)
    fcR := div_known hmR hT (by decide) }

/-- The same for a layout that the verifier returns. -/
theorem numH_of_layout {h : Model.Head.Shape} {tau : Array F} {L : HL} (hF : FullH h)
    (hL : Model.Head.layout h tau = .ok L) : NumH h L := numH_of_laid hF (laidH_of_layout hL)

/-! ## The matrix of the stream -/

/-- The verifier's record of the stream's matrix, as numerals: the columns, the rows, the features
of a column, and the feature of limb l of channel j, which is the library's fX l j. -/
structure BorderH (b : Border) : Prop where
  kxb : b.kxb = 400
  mxb : b.mxb = 65536
  fc : b.mxb / 1024 = 64
  cell : ∀ l j, b.cell l j = Inst.Model.Head.fX l j

/-- The record that the head is given of a layers' layout whose sizes are the library's reference
sizes. -/
theorem borderH_of_laid {y : Lay} (L1 : OnBytes.Road.Laid y) (L2 : Laid2 y) (S : Switches y.h)
    (Z : Sized y.h DF) (Z2 : Sized2 y.h DF) : BorderH (borderOf y) := by
  have hk : y.kxb = 400 :=
    ((nCol_eq L2 S Z Z2).2.2.2.2.2).trans Inst.Model.FFSeg.ref_shapes.2.2.2.2.2.2.2.1
  have hm : y.mxb = 65536 :=
    (rowsM_eq L2 Z Z2 (μ := .xout) (by decide)).trans Cm.Seg.ffRow_xout
  have hd : y.h.d = 5120 := Z.d.symm
  refine ⟨hk, hm, div_known hm rfl (by decide), fun l j => ?_⟩
  show tenCell y.xb l 0 j = 5120 * l + j
  rw [L1.xb]
  show 0 + (l * 1 + 0) * y.h.d + j = 5120 * l + j
  rw [hd]
  omega

/-- The same for a layout that the verifier returns. -/
theorem borderH_of_layout {hy : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF)
    (Z2 : Sized2 hy DF) : BorderH (borderOf y) := by
  obtain ⟨e, L1⟩ := laid_of_layout hl S.p3
  subst e
  exact borderH_of_laid L1 (laid2_of_layout hl) S Z Z2

/-! ## The verifier's rule is the library's row and column -/

/-- A column of the library's matrix x holds 64 features. -/
theorem perCol_x : perCol .x = 64 := by decide

section Rule

variable {h : Model.Head.Shape} {L : HL} (N : NumH h L)

include N in
/-- hf: the row is the library's, and the column, counted across the parts, is the library's. -/
theorem placeIn_hf (φ i : ℕ) :
    ((placeIn L.k (L.m / h.T) h.T φ i).2.1,
      (placeIn L.k (L.m / h.T) h.T φ i).1 * L.k + (placeIn L.k (L.m / h.T) h.T φ i).2.2) =
      (rowOf .hf φ i, colOf .hf φ) := by
  rw [N.k, N.fc, N.T]
  unfold rowOf colOf
  rw [Cm.Seg.perCol_hf]
  show (φ % 64 * 1024 + i, φ / 64 / 4816 * 4816 + φ / 64 % 4816) = (φ % 64 * 2 ^ 10 + i, φ / 64)
  rw [Prod.mk.injEq]
  exact ⟨by omega, by omega⟩

include N in
/-- hd. -/
theorem placeIn_hd (φ i : ℕ) :
    ((placeIn L.kD (L.mD / h.T) h.T φ i).2.1,
      (placeIn L.kD (L.mD / h.T) h.T φ i).1 * L.kD + (placeIn L.kD (L.mD / h.T) h.T φ i).2.2) =
      (rowOf .hd φ i, colOf .hd φ) := by
  rw [N.kD, N.fcD, N.T]
  unfold rowOf colOf
  rw [Cm.Seg.perCol_hd]
  show (φ % 16 * 1024 + i, φ / 16 / 640 * 640 + φ / 16 % 640) = (φ % 16 * 2 ^ 10 + i, φ / 16)
  rw [Prod.mk.injEq]
  exact ⟨by omega, by omega⟩

include N in
/-- hr. -/
theorem placeIn_hr (φ i : ℕ) :
    ((placeIn L.kR (L.mR / h.T) h.T φ i).2.1,
      (placeIn L.kR (L.mR / h.T) h.T φ i).1 * L.kR + (placeIn L.kR (L.mR / h.T) h.T φ i).2.2) =
      (rowOf .hr φ i, colOf .hr φ) := by
  rw [N.kR, N.fcR, N.T]
  unfold rowOf colOf
  rw [Cm.Seg.perCol_hr]
  show (φ % 8 * 1024 + i, φ / 8 / 15 * 15 + φ / 8 % 15) = (φ % 8 * 2 ^ 10 + i, φ / 8)
  rw [Prod.mk.injEq]
  exact ⟨by omega, by omega⟩

include N in
/-- The stream: the feature that the verifier's record gives limb φ / d of channel φ mod d is φ, and
its row and column are the library's. -/
theorem placeIn_x {b : Border} (Bd : BorderH b) (φ i : ℕ) :
    b.cell (φ / h.d) (φ % h.d) = φ ∧
    ((placeIn b.kxb (b.mxb / h.T) h.T φ i).2.1,
      (placeIn b.kxb (b.mxb / h.T) h.T φ i).1 * b.kxb + (placeIn b.kxb (b.mxb / h.T) h.T φ i).2.2) =
      (rowOf .x φ i, colOf .x φ) := by
  refine ⟨?_, ?_⟩
  · rw [Bd.cell, N.d]
    exact Nat.div_add_mod φ 5120
  · rw [N.T, Bd.fc, Bd.kxb]
    unfold rowOf colOf
    rw [perCol_x]
    show (φ % 64 * 1024 + i, φ / 64 / 400 * 400 + φ / 64 % 400) = (φ % 64 * 2 ^ 10 + i, φ / 64)
    rw [Prod.mk.injEq]
    exact ⟨by omega, by omega⟩

include N in
/-- A cell of a feature that the matrix has, at a position below T, stands inside a part that the
list has. hf has 128 features more than the library's cells: they fill the last part. -/
theorem placeIn_inside {b : Border} (Bd : BorderH b) {φ i : ℕ} (hi : i < 1024) :
    (φ < nFeat .hf + 128 → (placeIn L.k (L.m / h.T) h.T φ i).1 < h.NHf ∧
      (placeIn L.k (L.m / h.T) h.T φ i).2.1 < L.m ∧ (placeIn L.k (L.m / h.T) h.T φ i).2.2 < L.k) ∧
    (φ < nFeat .hd → (placeIn L.kD (L.mD / h.T) h.T φ i).1 = 0 ∧
      (placeIn L.kD (L.mD / h.T) h.T φ i).2.1 < L.mD ∧
      (placeIn L.kD (L.mD / h.T) h.T φ i).2.2 < L.kD) ∧
    (φ < nFeat .hr → (placeIn L.kR (L.mR / h.T) h.T φ i).1 = 0 ∧
      (placeIn L.kR (L.mR / h.T) h.T φ i).2.1 < L.mR ∧
      (placeIn L.kR (L.mR / h.T) h.T φ i).2.2 < L.kR) ∧
    (φ < nFeat .x → (placeIn b.kxb (b.mxb / h.T) h.T φ i).1 = 0 ∧
      (placeIn b.kxb (b.mxb / h.T) h.T φ i).2.1 < b.mxb ∧
      (placeIn b.kxb (b.mxb / h.T) h.T φ i).2.2 < b.kxb) := by
  rw [N.fc, N.fcD, N.fcR, N.T, Bd.fc, N.k, N.kD, N.kR, N.m, N.mD, N.mR, N.NHf, Bd.kxb, Bd.mxb]
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩
  · have hφ' : φ < 1232768 + 128 := hφ
    show φ / 64 / 4816 < 4 ∧ φ % 64 * 1024 + i < 65536 ∧ φ / 64 % 4816 < 4816
    omega
  · have hφ' : φ < 10240 := hφ
    show φ / 16 / 640 = 0 ∧ φ % 16 * 1024 + i < 16384 ∧ φ / 16 % 640 < 640
    omega
  · have hφ' : φ < 120 := hφ
    show φ / 8 / 15 = 0 ∧ φ % 8 * 1024 + i < 8192 ∧ φ / 8 % 15 < 15
    omega
  · have hφ' : φ < 25600 := hφ
    show φ / 64 / 400 = 0 ∧ φ % 64 * 1024 + i < 65536 ∧ φ / 64 % 400 < 400
    omega

end Rule

/-! ## The cells, written out at the full size -/

section Cells

variable {K : Type} {h : Model.Head.Shape} {L : HL} (N : NumH h L) (b : Border) (M : Mats K)

include N in
/-- A cell of hf. -/
theorem hf_at (φ i : ℕ) :
    (cellsH h L b M).hf φ i = M (φ / 64 / 4816) (φ % 64 * 1024 + i) (φ / 64 % 4816) := by
  show cellIn M 0 L.k (L.m / h.T) h.T φ i = _
  rw [N.k, N.fc, N.T]
  unfold cellIn
  rw [Nat.zero_add]

include N in
/-- A cell of hd. -/
theorem hd_at {φ : ℕ} (hφ : φ < 10240) (i : ℕ) :
    (cellsH h L b M).hd φ i = M 4 (φ % 16 * 1024 + i) (φ / 16) := by
  show cellIn M h.NHf L.kD (L.mD / h.T) h.T φ i = _
  rw [N.NHf, N.kD, N.fcD, N.T]
  unfold cellIn
  have e1 : 4 + φ / 16 / 640 = 4 := by omega
  have e2 : φ / 16 % 640 = φ / 16 := by omega
  rw [e1, e2]

include N in
/-- A cell of hr. -/
theorem hr_at {φ : ℕ} (hφ : φ < 120) (i : ℕ) :
    (cellsH h L b M).hr φ i = M 5 (φ % 8 * 1024 + i) (φ / 8) := by
  show cellIn M (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i = _
  rw [N.NHf, N.kR, N.fcR, N.T]
  unfold cellIn
  have e1 : 4 + 1 + φ / 8 / 15 = 5 := by omega
  have e2 : φ / 8 % 15 = φ / 8 := by omega
  rw [e1, e2]

include N in
/-- A cell of the stream. -/
theorem x_at (Bd : BorderH b) {φ : ℕ} (hφ : φ < 25600) (i : ℕ) :
    (cellsH h L b M).x φ i = M 7 (φ % 64 * 1024 + i) (φ / 64) := by
  show cellIn M (h.NHf + 3) b.kxb (b.mxb / h.T) h.T (b.cell (φ / h.d) (φ % h.d)) i = _
  rw [(placeIn_x N Bd φ i).1, N.NHf, N.T, Bd.fc, Bd.kxb]
  unfold cellIn
  have e1 : 4 + 3 + φ / 64 / 400 = 7 := by omega
  have e2 : φ / 64 % 400 = φ / 64 := by omega
  rw [e1, e2]

end Cells

/-! ## The library's places, written out -/

/-- The place of a cell of hf. -/
theorem place_hf (φ i : ℕ) : (Name.hf φ i).place =
    (24, (0 + φ / 64 / 4816) * 65536 + (φ % 64 * 2 ^ 10 + i), φ / 64 % 4816) := by
  show (24, stack colsHead 0 (rowOf .hf φ i) (colOf .hf φ)) = _
  unfold stack rowOf colOf
  rw [Cm.Seg.colsHead_eq, Cm.Seg.hSlot_eq, Cm.Seg.perCol_hf]

/-- The place of a cell of hd. -/
theorem place_hd (φ i : ℕ) : (Name.hd φ i).place =
    (24, (4 + φ / 16 / 4816) * 65536 + (φ % 16 * 2 ^ 10 + i), φ / 16 % 4816) := by
  show (24, stack colsHead 4 (rowOf .hd φ i) (colOf .hd φ)) = _
  unfold stack rowOf colOf
  rw [Cm.Seg.colsHead_eq, Cm.Seg.hSlot_eq, Cm.Seg.perCol_hd]

/-- The place of a cell of hr. -/
theorem place_hr (φ i : ℕ) : (Name.hr φ i).place =
    (24, (5 + φ / 8 / 4816) * 65536 + (φ % 8 * 2 ^ 10 + i), φ / 8 % 4816) := by
  show (24, stack colsHead 5 (rowOf .hr φ i) (colOf .hr φ)) = _
  unfold stack rowOf colOf
  rw [Cm.Seg.colsHead_eq, Cm.Seg.hSlot_eq, Cm.Seg.perCol_hr]

/-- The library's address of the cell under which the head reads feature φ of the stream: the matrix
xout of a feed-forward segment, and the head's own row and column (addr_head). -/
theorem addr_x (φ i : ℕ) :
    Inst.Model.FFSeg.addr DF ⟨.x8, φ / 5120, 0, φ % 5120, i⟩ =
      (.xout, rowOf .x φ i, colOf .x φ) :=
  Prod.ext rfl (Inst.Model.All.addr_head φ i)

/-- The place of the cell under which the head reads feature φ of the stream: slot 7 of the last
feed-forward segment, which has the number 22. -/
theorem place_x (φ i : ℕ) : (ownX φ i).place =
    (22, (7 + φ / 64 / 5990) * 65536 + (φ % 64 * 2 ^ 10 + i), φ / 64 % 5990) := by
  show (2 * (nGr - 1), Cm.Seg.plFF ⟨.x8, φ / 5120, 0, φ % 5120, i⟩) = _
  unfold Cm.Seg.plFF
  rw [addr_x]
  show (2 * (nGr - 1), stack colsFF 7 (rowOf .x φ i) (colOf .x φ)) = _
  unfold stack rowOf colOf
  rw [Cm.Seg.colsFF_eq, Cm.Seg.hSlot_eq, perCol_x, Cm.Seg.nGr_eq]

/-! ## The dictionary -/

/-- The number, in the list of matrices of a layer sub-proof, of the matrix that stands in a slot of
the library's one matrix of a feed-forward segment. The library's slots are af in three parts, ad,
ar, qa, xin, xout. The verifier's list has another order: the parts of af, ad, ar, b, qa, the stream
that goes out, the stream that comes in (matIx in OnBytes/Model/LayerForms.lean). -/
def slotNo (y : Lay) : ℕ → ℕ
  | 3 => firstM y 1
  | 4 => firstM y 2
  | 5 => firstM y 3
  | 6 => firstM y 4
  | 7 => firstM y 5
  | s => firstM y 0 + s

/-- The library's family of matrices, one for each segment, made from the verifier's lists. Mg g:
the list of the layer sub-proof of group g. Mh: the list of the head's sub-proof. Ma g: the matrix
of the attention segment of group g, of which nothing is said here. Row r of a segment's matrix is
row r mod 2^16 of the matrix in slot r / 2^16. In the head's segment, number 24, the slot is the
number in the head's list: the four parts of hf, hd, hr. In the feed-forward segment 2 g it is
slotNo. A matrix of a list is a function on all rows and columns, and it is handed on as it is: past
a matrix's own rows and columns, in the slots 6 and 7 of segment 24 (bH and the head's own copy of
the stream) and in the slots from 8 on, the family holds whatever the lists hold there, not 0 as the
matrices that the library makes from a trace. The theorems of this file read the family at the
places of features that hold a cell (stacked_hf, stacked_hd, stacked_hr, stacked_x) and nowhere
else. -/
def stackedH {K : Type} (y : Lay) (Mg : ℕ → Mats K) (Ma : ℕ → ℕ → ℕ → K) (Mh : Mats K) :
    ℕ → ℕ → ℕ → K := fun s r c =>
  if s = 24 then Mh (r / 2 ^ 16) (r % 2 ^ 16) c
  else if s % 2 = 0 then Mg (s / 2) (slotNo y (r / 2 ^ 16)) (r % 2 ^ 16) c
  else Ma (s / 2) r c

/-- The matrix that the head borrows has the entries of the lender's matrix: number NHf + 3 of the
head's list against the stream that goes out in the list of the last group of layers. -/
def LentH {K : Type} (h : Model.Head.Shape) (y : Lay) (Mh Mlast : Mats K) : Prop :=
  ∀ r < 65536, ∀ c < 400, Mh (h.NHf + 3) r c = Mlast (firstM y 5) r c

section Stacked

variable {K : Type} (y : Lay) (Mg : ℕ → Mats K) (Ma : ℕ → ℕ → ℕ → K) (Mh : Mats K)

/-- The head's segment. -/
theorem stackedH_24 (r c : ℕ) :
    stackedH y Mg Ma Mh 24 r c = Mh (r / 2 ^ 16) (r % 2 ^ 16) c := if_pos rfl

/-- The last feed-forward segment. -/
theorem stackedH_22 (r c : ℕ) :
    stackedH y Mg Ma Mh 22 r c = Mg 11 (slotNo y (r / 2 ^ 16)) (r % 2 ^ 16) c :=
  (if_neg (by decide)).trans (if_pos (by decide))

variable {h : Model.Head.Shape} {L : HL} (N : NumH h L) (b : Border)

include N in
/-- At the library's place of a cell of hf the stacked matrices hold the verifier's cell. -/
theorem stacked_hf (φ : ℕ) {i : ℕ} (hi : i < 1024) :
    stackedH y Mg Ma Mh (Name.hf φ i).place.1 (Name.hf φ i).place.2.1 (Name.hf φ i).place.2.2 =
      (cellsH h L b Mh).hf φ i := by
  rw [place_hf, hf_at N]
  show stackedH y Mg Ma Mh 24 ((0 + φ / 64 / 4816) * 65536 + (φ % 64 * 2 ^ 10 + i))
    (φ / 64 % 4816) = _
  rw [stackedH_24]
  have e1 : ((0 + φ / 64 / 4816) * 65536 + (φ % 64 * 2 ^ 10 + i)) / 2 ^ 16 = φ / 64 / 4816 := by
    omega
  have e2 : ((0 + φ / 64 / 4816) * 65536 + (φ % 64 * 2 ^ 10 + i)) % 2 ^ 16 =
      φ % 64 * 1024 + i := by omega
  rw [e1, e2]

include N in
/-- The same for hd. -/
theorem stacked_hd {φ i : ℕ} (hφ : φ < 10240) (hi : i < 1024) :
    stackedH y Mg Ma Mh (Name.hd φ i).place.1 (Name.hd φ i).place.2.1 (Name.hd φ i).place.2.2 =
      (cellsH h L b Mh).hd φ i := by
  rw [place_hd, hd_at N b Mh hφ]
  show stackedH y Mg Ma Mh 24 ((4 + φ / 16 / 4816) * 65536 + (φ % 16 * 2 ^ 10 + i))
    (φ / 16 % 4816) = _
  rw [stackedH_24]
  have e1 : ((4 + φ / 16 / 4816) * 65536 + (φ % 16 * 2 ^ 10 + i)) / 2 ^ 16 = 4 := by omega
  have e2 : ((4 + φ / 16 / 4816) * 65536 + (φ % 16 * 2 ^ 10 + i)) % 2 ^ 16 =
      φ % 16 * 1024 + i := by omega
  have e3 : φ / 16 % 4816 = φ / 16 := by omega
  rw [e1, e2, e3]

include N in
/-- The same for hr. -/
theorem stacked_hr {φ i : ℕ} (hφ : φ < 120) (hi : i < 1024) :
    stackedH y Mg Ma Mh (Name.hr φ i).place.1 (Name.hr φ i).place.2.1 (Name.hr φ i).place.2.2 =
      (cellsH h L b Mh).hr φ i := by
  rw [place_hr, hr_at N b Mh hφ]
  show stackedH y Mg Ma Mh 24 ((5 + φ / 8 / 4816) * 65536 + (φ % 8 * 2 ^ 10 + i))
    (φ / 8 % 4816) = _
  rw [stackedH_24]
  have e1 : ((5 + φ / 8 / 4816) * 65536 + (φ % 8 * 2 ^ 10 + i)) / 2 ^ 16 = 5 := by omega
  have e2 : ((5 + φ / 8 / 4816) * 65536 + (φ % 8 * 2 ^ 10 + i)) % 2 ^ 16 =
      φ % 8 * 1024 + i := by omega
  have e3 : φ / 8 % 4816 = φ / 8 := by omega
  rw [e1, e2, e3]

/-- At the library's place of the cell under which the head reads the stream, the stacked matrices
hold an entry of the lender's matrix: the stream that goes out of the last group of layers. -/
theorem stacked_own {φ i : ℕ} (hφ : φ < 25600) (hi : i < 1024) :
    stackedH y Mg Ma Mh (ownX φ i).place.1 (ownX φ i).place.2.1 (ownX φ i).place.2.2 =
      Mg 11 (firstM y 5) (φ % 64 * 1024 + i) (φ / 64) := by
  rw [place_x]
  show stackedH y Mg Ma Mh 22 ((7 + φ / 64 / 5990) * 65536 + (φ % 64 * 2 ^ 10 + i))
    (φ / 64 % 5990) = _
  rw [stackedH_22]
  have e1 : ((7 + φ / 64 / 5990) * 65536 + (φ % 64 * 2 ^ 10 + i)) / 2 ^ 16 = 7 := by omega
  have e2 : ((7 + φ / 64 / 5990) * 65536 + (φ % 64 * 2 ^ 10 + i)) % 2 ^ 16 =
      φ % 64 * 1024 + i := by omega
  have e3 : φ / 64 % 5990 = φ / 64 := by omega
  rw [e1, e2, e3]
  rfl

include N in
/-- The same for the stream, if the borrowed matrix has the lender's entries. -/
theorem stacked_x (Bd : BorderH b) (hl : LentH h y Mh (Mg 11)) {φ i : ℕ} (hφ : φ < 25600)
    (hi : i < 1024) :
    stackedH y Mg Ma Mh (ownX φ i).place.1 (ownX φ i).place.2.1 (ownX φ i).place.2.2 =
      (cellsH h L b Mh).x φ i := by
  have e : Mh 7 (φ % 64 * 1024 + i) (φ / 64) =
      Mg 11 (firstM y 5) (φ % 64 * 1024 + i) (φ / 64) := by
    have e0 := hl (φ % 64 * 1024 + i) (by omega) (φ / 64) (by omega)
    rw [N.NHf] at e0
    exact e0
  rw [stacked_own y Mg Ma Mh hφ hi, x_at N b Mh Bd hφ, e]

end Stacked

/-! ## Lender and borrower read one cell -/

section Lender

variable {K : Type} {y : Lay} (L2 : Laid2 y) (S : Switches y.h) (Z : Sized y.h DF)
  (Z2 : Sized2 y.h DF)

include L2 S Z Z2 in
/-- The cell x8 of the last feed-forward segment under which the head reads feature φ of the stream,
read in the lender's own list by the rule of the layers' tables: it is the entry of the stream that
goes out, at the head's row and column. -/
theorem lender_x (Mlast : Mats K) {φ i : ℕ} (hφ : φ < 25600) (hi : i < 1024) :
    cellsOf DF (cellsAt y Mlast) ⟨.x8, φ / 5120, 0, φ % 5120, i⟩ =
      Mlast (firstM y 5) (φ % 64 * 1024 + i) (φ / 64) := by
  have hv0 : nGr - 1 < nGr ∧
      (⟨.x8, φ / 5120, 0, φ % 5120, i⟩ : Inst.Model.FFSeg.Cell).Valid DF ∧
      (Inst.Model.FFSeg.Arr.x8 = .x0 → nGr - 1 = 0) :=
    (Cm.lay_own_valid Cm.Seg.Hd.plain).2.2 φ hφ i hi
  rw [cells_addr L2 S Z Z2 Mlast _ hv0.2.1
      (fun e => absurd (show Inst.Model.FFSeg.Arr.x8 = .o from e) (by decide)), addr_x,
    atAddr_ne y DF Mlast (μ := .xout) (by decide)]
  unfold rowOf colOf
  rw [perCol_x]
  rfl

include L2 S Z Z2 in
/-- Lender and borrower read one cell: the head's cell of feature φ of the stream is the cell x8 of
the last group's layer sub-proof, if the borrowed matrix has the lender's entries. -/
theorem one_cell_x {h : Model.Head.Shape} {L : HL} (N : NumH h L) (L1 : OnBytes.Road.Laid y)
    (Mh Mlast : Mats K) (hl : LentH h y Mh Mlast) {φ i : ℕ} (hφ : φ < 25600) (hi : i < 1024) :
    (cellsH h L (borderOf y) Mh).x φ i =
      cellsOf DF (cellsAt y Mlast) ⟨.x8, φ / 5120, 0, φ % 5120, i⟩ := by
  have e : Mh 7 (φ % 64 * 1024 + i) (φ / 64) =
      Mlast (firstM y 5) (φ % 64 * 1024 + i) (φ / 64) := by
    have e0 := hl (φ % 64 * 1024 + i) (by omega) (φ / 64) (by omega)
    rw [N.NHf] at e0
    exact e0
  rw [lender_x L2 S Z Z2 Mlast hφ hi, x_at N _ Mh (borderH_of_laid L1 L2 S Z Z2) hφ, e]

end Lender

/-! ## In the library's own records -/

section Records

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-- The library's record ReadsAt, which its theorem head_holds_int asks for: the integer cells that
are read in the verifier's matrices by the verifier's rule are what the stacked matrices hold at the
places of the names that the plain head reads. -/
theorem readsAt_cellsH (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11)) :
    Cm.Spec.ReadsAt (cellsH h L (borderOf y) Mh) (stackedH y Mg Ma Mh) :=
  have N := numH_of_layout hF hL
  have Bd := borderH_of_layout hl S Z Z2
  ⟨fun φ _ _ hi => (stacked_hf y Mg Ma Mh N _ φ hi).symm,
    fun _ hφ _ hi => (stacked_hd y Mg Ma Mh N _ hφ hi).symm,
    fun _ hφ _ hi => (stacked_hr y Mg Ma Mh N _ (Nat.lt_of_lt_of_le hφ (by decide)) hi).symm,
    fun _ hφ _ hi => (stacked_x y Mg Ma Mh N _ Bd hlent hφ hi).symm⟩

/-- The same for the head with the acceptance policy's ledger, which reads all features of hf and
all 120 bytes of hr. -/
theorem readsAtMain_cellsH (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11)) :
    Policy.ReadsAtMain (cellsH h L (borderOf y) Mh) (stackedH y Mg Ma Mh) :=
  have N := numH_of_layout hF hL
  have Bd := borderH_of_layout hl S Z Z2
  ⟨fun φ _ _ hi => (stacked_hf y Mg Ma Mh N _ φ hi).symm,
    fun _ hφ _ hi => (stacked_hd y Mg Ma Mh N _ hφ hi).symm,
    fun _ hφ _ hi => (stacked_hr y Mg Ma Mh N _ hφ hi).symm,
    fun _ hφ _ hi => (stacked_x y Mg Ma Mh N _ Bd hlent hφ hi).symm⟩

/-- The same over the extension field: the library's reading tH of the stacked matrices is cellsH,
at every feature that holds a cell and every position. -/
theorem tH_cellsH (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats Cb.Gl.E) (Ma : ℕ → ℕ → ℕ → Cb.Gl.E) (Mh : Mats Cb.Gl.E)
    (hlent : LentH h y Mh (Mg 11)) {i : ℕ} (hi : i < nT) :
    (∀ φ, (Cm.Seg.TS.tH (stackedH y Mg Ma Mh)).hf φ i = (cellsH h L (borderOf y) Mh).hf φ i) ∧
    (∀ φ < nFeat .hd,
      (Cm.Seg.TS.tH (stackedH y Mg Ma Mh)).hd φ i = (cellsH h L (borderOf y) Mh).hd φ i) ∧
    (∀ φ < nFeat .hr,
      (Cm.Seg.TS.tH (stackedH y Mg Ma Mh)).hr φ i = (cellsH h L (borderOf y) Mh).hr φ i) ∧
    ∀ φ < nFeat .x,
      (Cm.Seg.TS.tH (stackedH y Mg Ma Mh)).x φ i = (cellsH h L (borderOf y) Mh).x φ i :=
  have N := numH_of_layout hF hL
  have Bd := borderH_of_layout hl S Z Z2
  ⟨fun φ => stacked_hf y Mg Ma Mh N _ φ hi, fun _ hφ => stacked_hd y Mg Ma Mh N _ hφ hi,
    fun _ hφ => stacked_hr y Mg Ma Mh N _ hφ hi,
    fun _ hφ => stacked_x y Mg Ma Mh N _ Bd hlent hφ hi⟩

/-- Stacking commutes with a map of the entries: the stacked matrices of the images are the images
of the stacked matrices. With the cast of the integers this is the library's castM. -/
theorem stackedH_map {K K' : Type} (f : K → K') (y : Lay) (Mg : ℕ → Mats K) (Ma : ℕ → ℕ → ℕ → K)
    (Mh : Mats K) (s r c : ℕ) :
    stackedH y (fun g a r c => f (Mg g a r c)) (fun g r c => f (Ma g r c))
      (fun a r c => f (Mh a r c)) s r c = f (stackedH y Mg Ma Mh s r c) := by
  unfold stackedH
  by_cases h1 : s = 24
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : s % 2 = 0
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]

end Records

#print axioms laidH_of_layout
#print axioms numH_of_layout
#print axioms borderH_of_layout
#print axioms placeIn_hf
#print axioms placeIn_hd
#print axioms placeIn_hr
#print axioms placeIn_x
#print axioms placeIn_inside
#print axioms one_cell_x
#print axioms readsAt_cellsH
#print axioms readsAtMain_cellsH
#print axioms tH_cellsH
#print axioms stackedH_map

end OnBytes.Road.Hd
