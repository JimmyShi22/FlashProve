-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysDictZ.lean: the dictionary of cells of a feed-forward segment, cut to the
shapes of the verifier's matrices; and the bound on the cells.

The library's law from the conditions of the segments to its relation asks that all entries of the
integer matrices are below 2^18 in absolute value at ALL places of a segment's rectangle of 2^19
rows and 5,990 columns, also where no cell stands. libM, libOf and libOfA
(Johnson/Road/FormsKeysDict.lean, Johnson/Road/FormsKeysDictA.lean) read the verifier's matrices at
such places too, outside the rows and columns that these matrices have. The matrices of this file
are 0 there. Then the library's bound follows from a bound on the entries that the verifier's
matrices have, with no other hypothesis; and the dictionary still holds, because the place of every
valid name lies inside the verifier's shapes.

What is compared with what. dict_mz, dict_z: the library's reading tM
(Cm/TargetSegFFAffPass.lean) of matrices of this file against cellsOf and cellsAt of these files.
small_mz, below_z: the library's InShape (Cm/SegLayout.lean) and Below (Cb/Part/LdPartDef.lean, at
targetPart of Cm/TargetPart.lean) at matrices of this file. shape_tails: rowsM and colsM of
Johnson/Road/FormsKeysMat.lean against the rows and columns in the verifier's own list tailsOf
(OnBytes/Model/LayerPlan.lean).

Main definitions, all of this file: slotMat, InZ, CutM, libMZ, SmallM; libOfZ, SmallA.
Main theorems.
 - addr_in: the library's address of a valid name lies inside the verifier's matrix.
 - cut_at: the place at which the library reads a valid name is a place that libMZ keeps.
 - dict_mz: for one group, tM g (libMZ y g Mz) is the verifier's cell at every valid name.
 - small_all, small_mz, small_z: if the entries of Mz inside the shapes are below 2^18, so are all
   entries of libMZ y g Mz; those of segment 2 g in the library's shape; and all cells.
 - dict_z, small_ofz, below_z: the same for all twelve groups in one family of matrices, named by
   the labels of the verifier's plan; below_z is the hypothesis Below (2 D) of the library's law.
 - shape_tails, shape_tails_ref: the rows and columns to which the matrices are cut are those of the
   verifier's list.

The hypotheses. dict_mz, dict_z, cut_at: those of dict_valid (FormsKeysDict.lean, whose head says
where they are met: at the full-size example alone). SmallM, SmallA: a bound on integers; the
matrices that are 0 meet it. That the matrices of an accepted proof meet it is what the verifier's
smallness test is there to deliver; no theorem of these files says so. small_all, small_mz,
small_ofz, below_z have no other hypothesis. shape_tails: three parts of af and one of ad;
shape_tails_ref has both from the hypotheses of dict_valid.

Which value is which: the entries of the matrices are hidden values, here any integers.

What is not claimed. What the heads of FormsKeysDict.lean and FormsKeysDictA.lean do not claim is
not claimed here: which number of the list is which matrix; that a matrix with an earlier group's
label is the matrix to which that group committed. The matrices of this file are 0 in the segments
of attention and of the head: the library's law asks its conditions and its bound of all 25
segments. The matrix b of the verifier's list holds no cell and is not read. The program does not
import this file.
-/
import Johnson.Road.FormsKeysDictA
import Cm.TargetPart

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Lay layout tailsOf matIx)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim Cell Arr Mx addr)
open Cm.Seg (at' plFF ownFF)

/-! ## The shapes -/

/-- The number that Johnson/Road/FormsKeysKit.lean gives to the matrix that fills a slot. -/
def slotMat : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | _ => 6

/-- Row r and column c lie in the verifier's matrix that fills slot σ. -/
@[reducible] def InZ (y : Lay) (σ r c : ℕ) : Prop :=
  σ < 8 ∧ r < rowsM y (slotMat σ) ∧ c < colsM y (slotMat σ)

instance (y : Lay) (σ r c : ℕ) : Decidable (InZ y σ r c) := by
  unfold InZ
  infer_instance

/-- The places that libMZ keeps: in segment 2 g the places inside the verifier's matrices, the slot
xin for the first group alone; and, for a later group, the places of the stream that comes in, in
the slot xout of segment 2 (g - 1). -/
@[reducible] def CutM (y : Lay) (g s r c : ℕ) : Prop :=
  (s = 2 * g ∧ InZ y (r / 65536) (r % 65536) c ∧ (r / 65536 = 6 → g = 0)) ∨
    (s + 2 = 2 * g ∧ r / 65536 = 7 ∧ InZ y 6 (r % 65536) c)

instance (y : Lay) (g s r c : ℕ) : Decidable (CutM y g s r c) := by
  unfold CutM
  infer_instance

/-- libM, cut to the shapes of the verifier's matrices: 0 at every other place. -/
def libMZ (y : Lay) (g : ℕ) (Mz : Mats ℤ) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if CutM y g s r c then libM y g Mz s r c else 0

/-! ## A valid name's place lies inside the shapes -/

section Inside

variable {y : Lay} (L : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
  (Z2 : Sized2 y.h D)

include L S Z Z2 in
/-- The library's address of a valid name lies inside the verifier's matrix: the row; and, in a
matrix in one part, the column. -/
theorem addr_in (q : Cell) (hv : q.Valid D) (ho : q.X = .o → y.h.p4 = true) :
    (addr D q).2.1 < rowsM y (mxNo (addr D q).1) ∧
      ((addr D q).1 ≠ .af → (addr D q).2.2 < colsM y (mxNo (addr D q).1)) := by
  obtain ⟨hk, hi, hj, hp⟩ := hv
  refine ⟨?_, fun ha => col_lt_cols L S Z Z2 hk hi hj ho ha⟩
  show Inst.Model.FFSeg.feat D q.X q.k q.inst q.j % 2 ^ Inst.Model.FFSeg.lFeat D q.X.mx * D.T +
    q.i < rowsM y (mxNo q.X.mx)
  have hfc := fcM_eq L Z2 (D := D) (Inst.Model.FFSeg.IndexFacts.mx_ne_b q.X)
  have h1 : fcM y (mxNo q.X.mx) * y.T ≤ rowsM y (mxNo q.X.mx) := Nat.div_mul_le_self _ _
  rw [hfc, T_eq L Z] at h1
  exact lt_of_lt_of_le
    (Inst.Model.FFSeg.IndexFacts.mr_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) hp) h1

end Inside

/-- The one array of the matrix xin is x0. -/
theorem mx_xin (X : Arr) (h : X.mx = .xin) : X = .x0 := by
  cases X <;> first | rfl | exact absurd h (by decide)

section Place

variable {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF)
  (hp4 : h.p4 = true)

include hy S Z Z2 hp4

/-- The place of a valid name in its own segment: it lies inside the verifier's matrix that fills
the slot, and the slot is xin for the array x0 alone. -/
theorem place_in (c : Cell) (hc : c.Valid DF) :
    InZ y ((plFF c).1 / 65536) ((plFF c).1 % 65536) (plFF c).2 ∧
      ((plFF c).1 / 65536 = 6 → c.X = .x0) := by
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  have L := laid2_of_layout hy
  obtain ⟨a1, a2⟩ := addr_in L S Z Z2 c hc fun _ => hp4
  have a3 : colsM y 0 = 5990 := (afCols_eq L S Z Z2).trans Cm.Seg.colsFF_eq
  have a4 : (addr DF c).1 = .xin → c.X = .x0 := fun hx => mx_xin c.X hx
  have B := Cm.Seg.ff_addr c hc
  unfold Cm.Seg.plFF Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Cm.Seg.colsFF_eq]
  generalize addr DF c = a at a1 a2 a4 B ⊢
  obtain ⟨μ, r, col⟩ := a
  rcases B with ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩
  · simp only at e b1 b2 a1
    subst e
    show InZ y (((0 + col / 5990) * 65536 + r) / 65536) (((0 + col / 5990) * 65536 + r) % 65536)
        (col % 5990) ∧ (((0 + col / 5990) * 65536 + r) / 65536 = 6 → c.X = .x0)
    have hq : col / 5990 < 3 := by omega
    have hm : col % 5990 < colsM y 0 := by
      rw [a3]
      exact Nat.mod_lt _ (by norm_num)
    generalize col / 5990 = q at hq ⊢
    rw [Nat.zero_add, (slot_div_mod (s := q) b1).1, (slot_div_mod (s := q) b1).2]
    refine ⟨⟨by omega, ?_, ?_⟩, fun h6 => absurd h6 (by omega)⟩
    · interval_cases q <;> exact a1
    · interval_cases q <;> exact hm
  all_goals
    simp only at e b1 b2 a1 a2 a4
    subst e
    have a2' := a2 (by decide)
    have h0 : col / 5990 = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : col % 5990 = col := Nat.mod_eq_of_lt (by omega)
    show InZ y (((_ + col / 5990) * 65536 + r) / 65536) (((_ + col / 5990) * 65536 + r) % 65536)
        (col % 5990) ∧ (((_ + col / 5990) * 65536 + r) / 65536 = 6 → c.X = .x0)
    rw [h0, h1, Nat.add_zero, (slot_div_mod b1).1, (slot_div_mod b1).2]
    dsimp only
    refine ⟨⟨by decide, a1, a2'⟩, fun h6 => ?_⟩
    first
      | exact a4 rfl
      | exact absurd h6 (by decide)

/-- The place at which the library reads a valid name of group g is a place that libMZ keeps. -/
theorem cut_at (g : ℕ) (c : Cell) (hc : c.Valid DF) :
    CutM y g (ownFF g c).place.1 (ownFF g c).place.2.1 (ownFF g c).place.2.2 := by
  by_cases hx : c.X = .x0 ∧ 0 < g
  · have e : ownFF g c = .ff (g - 1) { c with X := .x8 } := by
      unfold Cm.Seg.ownFF
      rw [if_pos hx]
    rw [e]
    obtain ⟨X, k, inst, j, i⟩ := c
    have hx' : X = .x0 := hx.1
    subst hx'
    obtain ⟨s1, -, -⟩ := x8_place k inst j i hc
    obtain ⟨⟨-, p2, p3⟩, -⟩ := place_in hy S Z Z2 hp4 ⟨.x8, k, inst, j, i⟩ hc
    rw [s1] at p2 p3
    refine Or.inr ⟨?_, s1, by decide, p2, p3⟩
    show 2 * (g - 1) + 2 = 2 * g
    omega
  · have e : ownFF g c = .ff g c := by
      unfold Cm.Seg.ownFF
      rw [if_neg hx]
    rw [e]
    obtain ⟨p1, p2⟩ := place_in hy S Z Z2 hp4 c hc
    refine Or.inl ⟨rfl, p1, fun h6 => ?_⟩
    by_contra hg
    exact hx ⟨p2 h6, Nat.pos_of_ne_zero hg⟩

/-- For one group. The library's reading of the matrices libMZ y g Mz as a trace of the feed-forward
segment of group g is, at every valid name, the cell that the verifier's rule reads in Mz. -/
theorem dict_mz (g : ℕ) (Mz : Mats ℤ) (c : Cell) (hc : c.Valid DF) :
    Cm.Seg.TS.tM g (libMZ y g Mz) c = cellsOf DF (cellsAt y Mz) c := by
  rw [← dict_valid hy S Z Z2 hp4 g Mz c hc]
  show libMZ y g Mz (ownFF g c).place.1 (ownFF g c).place.2.1 (ownFF g c).place.2.2 =
    libM y g Mz (ownFF g c).place.1 (ownFF g c).place.2.1 (ownFF g c).place.2.2
  unfold libMZ
  rw [if_pos (cut_at hy S Z Z2 hp4 g c hc)]

end Place

/-! ## The bound -/

/-- The entries of the verifier's matrices that hold cells, inside their shapes, are below 2^18 in
absolute value. -/
def SmallM (y : Lay) (Mz : Mats ℤ) : Prop :=
  ∀ σ r c, InZ y σ r c → |Mz (portNo y σ) r c| < 2 ^ 18

/-- Then all entries of libMZ y g Mz are. -/
theorem small_all {y : Lay} {Mz : Mats ℤ} (H : SmallM y Mz) (g s r c : ℕ) :
    |libMZ y g Mz s r c| < 2 ^ 18 := by
  unfold libMZ
  by_cases hC : CutM y g s r c
  · rw [if_pos hC]
    unfold libM
    rcases hC with ⟨e, hz, -⟩ | ⟨e, h7, hz⟩
    · rw [if_pos e]
      exact H _ _ _ hz
    · rw [if_neg (by omega), if_pos ⟨e, h7⟩]
      exact H 6 _ _ hz
  · rw [if_neg hC]
    norm_num

/-- In the letters of the library's shape: the entries of segment 2 g. -/
theorem small_mz {y : Lay} {Mz : Mats ℤ} (H : SmallM y Mz) (g : ℕ) :
    ∀ r c, Cm.Seg.InShape (2 * g, r, c) → |libMZ y g Mz (2 * g) r c| < 2 ^ 18 :=
  fun r c _ => small_all H g (2 * g) r c

/-- The cells: the clause small of the library's relation over the integers (IntRel in
Inst/Model/FF/NoWrap0.lean), at the trace that the library reads in libMZ y g Mz. -/
theorem small_z {y : Lay} {Mz : Mats ℤ} (H : SmallM y Mz) (g : ℕ) (c : Cell) :
    |Cm.Seg.TS.tM g (libMZ y g Mz) c| < 2 ^ 18 :=
  small_all H g _ _ _

/-! ## All twelve groups, by the labels -/

/-- libOfA, cut to the shapes of the verifier's matrices; the slot xin is kept for the first group
alone. -/
def libOfZ (y : Lay) (Ma : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if InZ y (r / 65536) (r % 65536) c ∧ (r / 65536 = 6 → s = 0) then libOfA y Ma s r c else 0

/-- The bound for the matrices of all twelve groups. -/
def SmallA (y : Lay) (Ma : ℕ → ℕ → ℕ → ℤ) : Prop := ∀ g, g < 12 → SmallM y (mzA y Ma g)

/-- Then all entries of libOfZ y Ma are below 2^18. -/
theorem small_ofz {y : Lay} {Ma : ℕ → ℕ → ℕ → ℤ} (H : SmallA y Ma) (s r c : ℕ) :
    |libOfZ y Ma s r c| < 2 ^ 18 := by
  unfold libOfZ
  by_cases hC : InZ y (r / 65536) (r % 65536) c ∧ (r / 65536 = 6 → s = 0)
  · rw [if_pos hC]
    unfold libOfA
    by_cases h2 : s % 2 = 0 ∧ s < 24
    · rw [if_pos h2]
      exact H (s / 2) (by omega) _ _ _ hC.1
    · rw [if_neg h2]
      norm_num
  · rw [if_neg hC]
    norm_num

/-- The hypothesis Below (2 D) of the library's law force, at the model's partition, for all letters
of the code's side and every table of scales. -/
theorem below_z {y : Lay} {Ma : ℕ → ℕ → ℕ → ℤ} (H : SmallA y Ma) (R : Cm.TargetRoom)
    (s : Cm.Scales) :
    (Cm.targetPart R s).Below (2 * (Cm.targetPart R s).D) (libOfZ y Ma) := by
  intro q _
  have h := small_ofz H q.1 q.2.1 q.2.2
  show |libOfZ y Ma q.1 q.2.1 q.2.2| < 2 * 2 ^ 17
  norm_num at h ⊢
  exact h

/-- For all twelve groups in one family of matrices. -/
theorem dict_z {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF)
    (hp4 : h.p4 = true) (Ma : ℕ → ℕ → ℕ → ℤ) {g : ℕ} (hg : g < 12) (c : Cell)
    (hc : c.Valid DF) :
    Cm.Seg.TS.tM g (libOfZ y Ma) c = cellsOf DF (cellsAt y (mzA y Ma g)) c := by
  rw [← dict_lab hy S Z Z2 hp4 Ma hg c hc]
  show libOfZ y Ma (ownFF g c).place.1 (ownFF g c).place.2.1 (ownFF g c).place.2.2 =
    libOfA y Ma (ownFF g c).place.1 (ownFF g c).place.2.1 (ownFF g c).place.2.2
  have C := cut_at hy S Z Z2 hp4 g c hc
  unfold libOfZ
  rcases C with ⟨e, hz, h6⟩ | ⟨-, h7, hz⟩
  · rw [if_pos ⟨hz, fun h => by have h0 := h6 h; omega⟩]
  · rw [if_pos ⟨by rw [h7]; exact ⟨by decide, hz.2.1, hz.2.2⟩, fun h => by omega⟩]

/-! ## The shapes are the verifier's -/

/-- The rows and columns to which the matrices are cut are those that the verifier's own list of
matrices gives the entry, in every group. -/
theorem shape_tails (y : Lay) (h3 : y.parts.getD 0 0 = 3) (h1 : y.parts.getD 1 0 = 1) {g σ : ℕ}
    (hg : g < y.NGr) (hσ : σ < 8) :
    (((tailsOf y).getD g {}).mats.getD (portNo y σ) {}).m = rowsM y (slotMat σ) ∧
      (((tailsOf y).getD g {}).mats.getD (portNo y σ) {}).k = colsM y (slotMat σ) := by
  have hn : portNo y σ < 9 ∧ portNo y σ = [0, 1, 2, 3, 4, 6, 8, 7].getD σ 0 := by
    have e1 : (matIx y).iAD = 3 := h3
    have e2 : (matIx y).iAR = 4 := by
      show y.parts.getD 0 0 + y.parts.getD 1 0 = 4
      omega
    have e3 : (matIx y).iQA = 6 := by
      show y.parts.getD 0 0 + y.parts.getD 1 0 + 2 = 6
      omega
    have e4 : (matIx y).iXO = 7 := by
      show y.parts.getD 0 0 + y.parts.getD 1 0 + 3 = 7
      omega
    have e5 : (matIx y).iXI = 8 := by
      show y.parts.getD 0 0 + y.parts.getD 1 0 + 4 = 8
      omega
    have e0 : (matIx y).iAF = 0 := rfl
    interval_cases σ <;> simp [portNo, firstM, e0, e1, e2, e3, e4, e5]
  unfold tailsOf
  dsimp only
  rw [range_map_at _ _ _ hg]
  dsimp only
  rw [h3, h1, hn.2]
  interval_cases σ <;> simp [rowsM, colsM, slotMat, List.zipIdx, List.range, List.range.loop] <;>
    split <;> simp

/-- The same for a layout that the verifier returns at the reference sizes. -/
theorem shape_tails_ref {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) (Z2 : Sized2 h DF) {g σ : ℕ} (hg : g < y.NGr)
    (hσ : σ < 8) :
    (((tailsOf y).getD g {}).mats.getD (portNo y σ) {}).m = rowsM y (slotMat σ) ∧
      (((tailsOf y).getD g {}).mats.getD (portNo y σ) {}).k = colsM y (slotMat σ) := by
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  have L := laid2_of_layout hy
  refine shape_tails y ?_ ?_ hg hσ
  · rw [L.parts0, ← Z2.parts]
    rfl
  · rw [L.parts1, Z2.NAd]

#print axioms addr_in
#print axioms place_in
#print axioms cut_at
#print axioms dict_mz
#print axioms small_all
#print axioms small_mz
#print axioms small_z
#print axioms small_ofz
#print axioms below_z
#print axioms dict_z
#print axioms shape_tails
#print axioms shape_tails_ref

end OnBytes.Road
