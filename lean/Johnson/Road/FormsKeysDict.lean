-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysDict.lean: the dictionary of cells of a feed-forward segment: the library's
one matrix of a segment, filled from the verifier's matrices.

The library's theorems on the segments of the model read the cells of a segment in one integer
matrix of 2^19 rows and 5,990 columns (Cm/SegLayout.lean): the matrices af, ad, ar, qa, xin, xout
stand one below the other in slots of 2^16 rows, and af, which is wider, is cut into three parts of
5,990 columns, which take three slots. Row and column inside a matrix are the library's address of
a cell (addr in Inst/Model/FF/Index.lean). The verifier has a list of matrices for each group of
layers, with af in parts. Johnson/Road/FormsKeysAddr.lean shows that the verifier's rule for a cell
is the library's address, with the same cutting of af. So a slot of the library's matrix is one
matrix of the list, namely the one that firstM (Johnson/Road/FormsKeysMat.lean) names for it. This
file writes that down and proves it.

What is compared with what: the library's reading tM of integer matrices as a trace of a segment
(Cm/TargetSegFFAffPass.lean; ownFF, place, plFF, stack, slotFF in Cm/SegLayout.lean) against
cellsOf and cellsAt (Johnson/Road/FormsKeysFits.lean, Johnson/Road/FormsKeysMat.lean), which read
the verifier's matrices by the rule of its tables of reads.

The seam. In a group after the first the library has no cell of the stream that comes in: the array
x0 of group g is read as x8 of group g - 1, in the slot xout of that group's segment. The verifier's
list for a group has a number for the stream that comes in; from the second group on its plan marks
that entry as the matrix to which the group before committed as its stream that goes out (tailsOf in
OnBytes/Model/LayerPlan.lean; by reading). These files give each group matrices of its own, so the
two are two letters, and Seam says that they are one. libM, for one group, lays the matrix with that
number where the library reads x0. libOf, for all groups in one family of matrices, cannot: the slot
is the earlier group's; there Seam is asked. Johnson/Road/FormsKeysDictA.lean names the matrices by
the plan's labels, and Seam holds by definition.

Main definitions: portNo, libM, libOf, Seam.
Main theorems.
 - slot_at: at the place of a valid name the slot's matrix holds the entry at the library's address.
 - dict_valid: for one group: tM g (libM y g Mz) is the verifier's cell at every valid name.
 - dict_all: for all groups in one family of matrices, with Seam.

The hypotheses. hy, S, Z, Z2, hp4: the verifier's layout returns; the switches; the sizes and the
matrices' sizes are the library's reference sizes; the profile is 4, at which the array o is a cell.
At the full-size example Johnson/Road/FormsKeysRunK.lean has S, Z and Z2 as theorems (switchesK,
sizedKF) and hy in a run; its profile is 4. That is the one witness given; the small example has
other sizes. Seam: no witness from a run of the verifier; made-up matrices meet it.
Johnson/Road/FormsKeysRunD.lean runs the conclusions at the full-size example's layout.
From that file's head, word for word: «D1 tM g (libM y g Mz) against the verifier's cell in Mz: the
conclusion of dict_valid. D2 tM g (libOf y Mz) against the verifier's cell in Mz g, at matrices in
which the stream that comes into a group is not what went out of the group before. D3 the same at
matrices in which it is (mzS): the conclusion of dict_all. The control, which must fail: D1 against
the verifier's cells in matrices with ar and qa in each other's place (mzX). What came out, and is
held by the guard. D1 and D3 fail nowhere. D2 fails nowhere in group 0, and in the groups 1 and 11
at the names of xin alone: there the library reads x8 of the group before. The control fails at the
names of ar and qa alone.»

Which value is which: the entries of the matrices are hidden values; here they are any integers.

What is not claimed. That the entries are small: the library's bound speaks of all places of a
segment's matrix, also of those where no cell stands, and libM and libOf read the verifier's
matrices there too. libM is 0 in the segments of attention and of the head; libOf is 0 in the
segments with an odd number, and from segment 24 on it reads Mz 12 and so on, which nobody fills.
Which number of the verifier's list is which matrix: libM and cellsAt are both of these files and
both go through firstM and mxNo, so a wrong number there would be seen by no theorem of this file
and by no guard of FormsKeysRunD.lean; the numbers are tied to the verifier's
tables of reads by
trueAt_of_holds (Johnson/Road/FormsKeysTrue.lean) alone, which no term joins with this file. The
program does not import this file.
-/
import Johnson.Road.FormsKeysAddr
import Cm.TargetSegFFAffPass
import Cm.SegLayoutProofs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Lay layout)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim Cell Arr Mx addr)
open Cm.Seg (at' plFF ownFF)

/-! ## The definitions -/

/-- The number, in the verifier's list of matrices, of the matrix that fills a slot of the library's
matrix of a segment: the three parts of af, ad, ar, qa, the stream that comes in, the stream that
goes out. -/
def portNo (y : Lay) : ℕ → ℕ
  | 0 => firstM y 0
  | 1 => firstM y 0 + 1
  | 2 => firstM y 0 + 2
  | 3 => firstM y 1
  | 4 => firstM y 2
  | 5 => firstM y 3
  | 6 => firstM y 4
  | 7 => firstM y 5
  | _ => 0

/-- The library's matrices for one group g, filled from the verifier's matrices Mz of that group:
segment 2 g slot by slot; and, for the array x0 of a later group, the matrix of the stream that
comes in, laid in the slot xout of segment 2 (g - 1), where the library reads it. 0 elsewhere. -/
def libM (y : Lay) (g : ℕ) (Mz : Mats ℤ) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if s = 2 * g then Mz (portNo y (r / 65536)) (r % 65536) c
  else if s + 2 = 2 * g ∧ r / 65536 = 7 then Mz (firstM y 4) (r % 65536) c
  else 0

/-- The library's matrices for all groups, filled from the verifier's matrices Mz g of each group.
0 in the segments with an odd number. From segment 24 on, which is the head's, it reads Mz 12 and so
on. -/
def libOf (y : Lay) (Mz : ℕ → Mats ℤ) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if s % 2 = 0 then Mz (s / 2) (portNo y (r / 65536)) (r % 65536) c else 0

/-- The matrix of the stream that comes into group g holds what the matrix of the stream that goes
out of group g - 1 holds. It is asked at all rows and columns; rows below 2^16 and columns below 400
would serve dict_all. -/
def Seam (y : Lay) (Mz : ℕ → Mats ℤ) (g : ℕ) : Prop :=
  ∀ r c, Mz g (firstM y 4) r c = Mz (g - 1) (firstM y 5) r c

/-! ## A slot is a matrix of the list -/

/-- The address of a cell of x8 is that of the cell of x0 with the same numbers, in the other
matrix. -/
theorem addr_x8 (D : Dim) (k inst j i : ℕ) :
    addr D ⟨.x8, k, inst, j, i⟩ = (.xout, (addr D ⟨.x0, k, inst, j, i⟩).2) := rfl

/-- The arithmetic of a slot. -/
theorem slot_div_mod {s r : ℕ} (hr : r < 65536) :
    (s * 65536 + r) / 65536 = s ∧ (s * 65536 + r) % 65536 = r := by
  constructor <;> omega

/-- A cell of x0 stands in the matrix xin. -/
theorem addr_x0_eta (D : Dim) (k inst j i : ℕ) :
    addr D ⟨.x0, k, inst, j, i⟩ =
      (.xin, (addr D ⟨.x0, k, inst, j, i⟩).2.1, (addr D ⟨.x0, k, inst, j, i⟩).2.2) := rfl

/-- A matrix that is not wider than a segment fills one slot. -/
theorem slot_other (y : Lay) (Mz : Mats ℤ) {k r col : ℕ} (hr : r < 65536) (hcol : col < 5990) :
    Mz (portNo y (((k + col / 5990) * 65536 + r) / 65536))
        (((k + col / 5990) * 65536 + r) % 65536) (col % 5990) =
      Mz (portNo y k) r col := by
  rw [Nat.div_eq_of_lt hcol, Nat.mod_eq_of_lt hcol, Nat.add_zero, (slot_div_mod hr).1,
    (slot_div_mod hr).2]

/-- At the place of a valid name, the matrix of the verifier's list that fills the slot holds the
entry at the library's address of the name. -/
theorem slot_at (y : Lay) (Mz : Mats ℤ) (c : Cell) (hc : c.Valid DF) :
    Mz (portNo y ((plFF c).1 / 65536)) ((plFF c).1 % 65536) (plFF c).2 =
      atAddr y DF Mz (addr DF c) := by
  have B := Cm.Seg.ff_addr c hc
  have hW : Inst.Model.FFSeg.afCols DF = 5990 := Cm.Seg.colsFF_eq
  unfold Cm.Seg.plFF Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Cm.Seg.colsFF_eq]
  generalize addr DF c = a at B ⊢
  obtain ⟨μ, r, col⟩ := a
  rcases B with ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩
  · simp only at e b1 b2
    subst e
    rw [atAddr_af, hW]
    show Mz (portNo y (((0 + col / 5990) * 65536 + r) / 65536))
      (((0 + col / 5990) * 65536 + r) % 65536) (col % 5990) = _
    have hq : col / 5990 < 3 := by omega
    generalize col / 5990 = q at hq ⊢
    rw [Nat.zero_add, (slot_div_mod (s := q) b1).1, (slot_div_mod (s := q) b1).2]
    interval_cases q <;> rfl
  all_goals
    simp only at e b1 b2
    subst e
    rw [atAddr_ne y DF Mz (by decide)]
    exact slot_other y Mz (r := r) (col := col) b1 (by omega)

/-- The place of a valid cell of x8: the slot xout, and there the row and the column of the cell of
x0 with the same numbers. -/
theorem x8_place (k inst j i : ℕ) (hc : Cell.Valid DF ⟨.x8, k, inst, j, i⟩) :
    (plFF ⟨.x8, k, inst, j, i⟩).1 / 65536 = 7 ∧
      (plFF ⟨.x8, k, inst, j, i⟩).1 % 65536 = (addr DF ⟨.x0, k, inst, j, i⟩).2.1 ∧
      (plFF ⟨.x8, k, inst, j, i⟩).2 = (addr DF ⟨.x0, k, inst, j, i⟩).2.2 := by
  have B := Cm.Seg.ff_addr ⟨.x8, k, inst, j, i⟩ hc
  unfold Cm.Seg.plFF Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Cm.Seg.colsFF_eq, addr_x8]
  rw [addr_x8] at B
  generalize (addr DF ⟨.x0, k, inst, j, i⟩).2 = a at B ⊢
  obtain ⟨r, col⟩ := a
  have b : r < 65536 ∧ col < 400 := by
    rcases B with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, b1, b2⟩
    · exact absurd e (by simp)
    · exact absurd e (by simp)
    · exact absurd e (by simp)
    · exact absurd e (by simp)
    · exact absurd e (by simp)
    · exact ⟨b1, b2⟩
  show ((7 + col / 5990) * 65536 + r) / 65536 = 7 ∧
    ((7 + col / 5990) * 65536 + r) % 65536 = r ∧ col % 5990 = col
  rw [Nat.div_eq_of_lt (show col < 5990 by omega), Nat.add_zero]
  exact ⟨(slot_div_mod b.1).1, (slot_div_mod b.1).2, Nat.mod_eq_of_lt (by omega)⟩

/-! ## The dictionary -/

section Dict

variable {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF)
  (hp4 : h.p4 = true)

include hy S Z Z2 hp4

/-- For one group. The library's reading of the matrices libM y g Mz as a trace of the feed-forward
segment of group g is, at every valid name, the cell that the verifier's rule reads in Mz. -/
theorem dict_valid (g : ℕ) (Mz : Mats ℤ) (c : Cell) (hc : c.Valid DF) :
    Cm.Seg.TS.tM g (libM y g Mz) c = cellsOf DF (cellsAt y Mz) c := by
  rw [cells_addr_of_layout hy S Z Z2 Mz c hc fun _ => hp4]
  show at' (libM y g Mz) (ownFF g c).place = _
  rcases Cm.Seg.ownFF_cases g c with e | ⟨h0, hx, e⟩
  · rw [e]
    show libM y g Mz (2 * g) (plFF c).1 (plFF c).2 = _
    unfold libM
    rw [if_pos rfl]
    exact slot_at y Mz c hc
  · rw [e]
    obtain ⟨X, k, inst, j, i⟩ := c
    have hx' : X = .x0 := hx
    subst hx'
    obtain ⟨s1, s2, s3⟩ := x8_place k inst j i hc
    show libM y g Mz (2 * (g - 1)) (plFF ⟨.x8, k, inst, j, i⟩).1 (plFF ⟨.x8, k, inst, j, i⟩).2 = _
    unfold libM
    rw [if_neg (by omega), if_pos ⟨by omega, s1⟩, s2, s3]
    generalize hA : addr DF ⟨.x0, k, inst, j, i⟩ = A
    have hm := addr_x0_eta DF k inst j i
    rw [hA] at hm
    rw [hm]
    exact (atAddr_ne y DF Mz (μ := .xin) (by decide) A.2.1 A.2.2).symm

/-- For all groups in one family of matrices. If the matrix that comes into group g holds what went
out of group g - 1 (asked for g > 0), the library's reading of libOf y Mz as a trace of the segment
of group g is, at every valid name, the cell that the verifier's rule reads in Mz g. -/
theorem dict_all (Mz : ℕ → Mats ℤ) (g : ℕ) (hseam : 0 < g → Seam y Mz g) (c : Cell)
    (hc : c.Valid DF) :
    Cm.Seg.TS.tM g (libOf y Mz) c = cellsOf DF (cellsAt y (Mz g)) c := by
  rw [← dict_valid hy S Z Z2 hp4 g (Mz g) c hc]
  show at' (libOf y Mz) (ownFF g c).place = at' (libM y g (Mz g)) (ownFF g c).place
  rcases Cm.Seg.ownFF_cases g c with e | ⟨h0, hx, e⟩
  · rw [e]
    show libOf y Mz (2 * g) (plFF c).1 (plFF c).2 = libM y g (Mz g) (2 * g) (plFF c).1 (plFF c).2
    unfold libOf libM
    rw [if_pos (by omega), if_pos rfl, show 2 * g / 2 = g by omega]
  · rw [e]
    obtain ⟨X, k, inst, j, i⟩ := c
    have hx' : X = .x0 := hx
    subst hx'
    obtain ⟨s1, -, -⟩ := x8_place k inst j i hc
    show libOf y Mz (2 * (g - 1)) (plFF ⟨.x8, k, inst, j, i⟩).1 (plFF ⟨.x8, k, inst, j, i⟩).2 =
      libM y g (Mz g) (2 * (g - 1)) (plFF ⟨.x8, k, inst, j, i⟩).1 (plFF ⟨.x8, k, inst, j, i⟩).2
    unfold libOf libM
    rw [if_pos (by omega), if_neg (by omega), if_pos ⟨by omega, s1⟩, s1,
      show 2 * (g - 1) / 2 = g - 1 by omega]
    exact (hseam h0 _ _).symm

end Dict

#print axioms slot_at
#print axioms x8_place
#print axioms dict_valid
#print axioms dict_all

end OnBytes.Road
