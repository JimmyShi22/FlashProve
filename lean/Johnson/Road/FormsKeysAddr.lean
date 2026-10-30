-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysAddr.lean: where a cell stands in the matrices of a layer sub-proof: the
verifier's rule against the library's address.

Johnson/Road/FormsKeysMat.lean defines cells from the entries of the matrices to which a prover
commits (cellsAt), by the rule that the verifier's tables of reads follow: feature φ at position i
stands in row (φ mod fc) T + i of column φ / fc, counted across the parts of its matrix. The library
has a rule of its own for the matrix, the row and the column of the cell with a given name (addr,
featAt, afPart in Inst/Model/FF/Index.lean). This file shows that the two rules give one place.

What is compared with what.
 - laid2_of_layout: the verifier's layout with itself: facts on the numbers that layout returns, in
   the words of layoutBase (OnBytes/Model/LayerLayout.lean). The record Laid2 gathers them.
 - feat_total: the verifier's count of the features in use in each matrix against the library's
   nFeatMx.
 - afCols_eq, rowsM_eq, nCol_eq, mZ_eq: the verifier's sizes of the matrices against the library's
   afCols, lRow, nCol, mZ.
 - cells_addr: cellsAt, a definition of these files after the verifier's rule, under the library's
   names of cells (cellsOf), against the library's addr. atAddr, which reads an address of the
   library in the verifier's matrices, is a definition of this file: it says which number of the
   verifier's list stands for which matrix of the library (firstM), and uses the library's afPart
   for the part of af.
 - place_inside, place_apart: on placeOf, the place that cellsAt reads, written out: a valid cell
   stands inside a part that the verifier's list has, and two valid cells stand at two places.

The hypotheses, and that they can be met.
 - Laid2 y: a conclusion, for every layout that layout returns (laid2_of_layout).
 - Switches y.h, Sized y.h D: as in Johnson/Road/FormsKeysFits.lean.
 - Sized2 y.h D: the library's sizes of the matrices agree with the shape. The library has one
   number for the features of a column of af, qa and the stream, and ad in one part; so, for a
   layout that layout returns, the record holds only of shapes with lmaf = lmq = lmx and NAd = 1.
   For every such shape sizes that meet Sized and Sized2 are there (sized_dimA). That layout returns
   for such a shape under the switches is no theorem here; it is a computation on public numbers.
 - q.Valid D: past the features of a matrix in one part the verifier's rule goes on into the next
   matrix of the list and the library's does not, so cells_addr is stated for valid names. In af
   the proof does not use it.
 - q.X = .o → profile 4: at profile 3 the verifier's matrix qa has no tensor o.
The library's Dim.OK is not asked. Its field blk says that 2^fBig divides the width of every array
of af, qa and the stream; with Sized2 that is the number of features of a column, which the verifier
does not ask to divide a width. The library's theorems addrInj and addrRange take Dim.OK; the parts
of their proofs that are needed here read of it only "there is a part", and are proved again without
it (feat_inj, af_col_lt).

What is not claimed. Nothing is said of the matrix b, of the order of the matrices in the library's
one matrix of a segment (Cm/SegLayout.lean), or of other sub-proofs that read qa and the stream.
That the verifier's tables of reads follow the rule of cellsAt is the matter of other files. mZ_eq's
left side is written with the layout's numbers and is not compared with a plan's list of matrices.
Nothing is a statement on what a verifier's acceptance shows. The program does not import this file.

-/
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysMat
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (refuseIf roundUp)
open OnBytes.Model.Layer (Lay Shape layout layoutBase layoutLook layTensors tensorAsks matrixSizes
  matIx)
open Inst.Model.FFSeg (Dim Cell Arr Mx)

/-! ## The sizes of the matrices, as the layout writes them -/

/-- The features in use in the four matrices af, ad, ar, qa: what layTensors returns beside the
tensors, on the list of tensors of the shape h. -/
def offsOf (h : Shape) : Array ℕ :=
  (layTensors (tensorAsks h (2 ^ h.ll) (2 ^ h.ll / 2) (h.H * h.dh + h.Gk * h.dh) (h.H * h.dh)
    (h.Gk * h.dh)) #[0, 0, 0, 0]).2

/-- The sizes of the four matrices, in the words of layoutBase (OnBytes/Model/LayerLayout.lean). -/
def sizesOf (h : Shape) : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (((offsOf h).toList.zip [h.lmaf, h.lmad, h.lmar, h.lmq]).zip [h.NAf, h.NAd, 1, 1]).map
    fun x => matrixSizes (2 ^ h.lt) x.1.1 x.1.2 x.2

/-- More plain facts on a layout's numbers, beside the record Laid: the positions, the sizes of the
matrices, and what the tests on these sizes have found. Each is the text of a line of layoutBase, or
follows from one of its tests. -/
structure Laid2 (y : Lay) : Prop where
  /-- the positions -/
  T : y.T = 2 ^ y.h.lt
  /-- the features in use -/
  feat : y.feat = ((sizesOf y.h).map (·.1)).toArray
  /-- the columns of a part -/
  kcol : y.kcol = ((sizesOf y.h).map (·.2.2.1)).toArray
  /-- the rows of a part -/
  mrow : y.mrow = ((sizesOf y.h).map (·.2.2.2.1)).toArray
  /-- the parts -/
  parts : y.parts = ((sizesOf y.h).map (·.2.2.2.2)).toArray
  /-- the rows of a matrix of the residual stream -/
  mxb : y.mxb = 2 ^ y.h.lmx
  /-- its columns -/
  kxb : y.kxb = roundUp (y.h.xl * y.h.d) (2 ^ y.h.lmx / 2 ^ y.h.lt) / (2 ^ y.h.lmx / 2 ^ y.h.lt)
  /-- a column of af, of qa and of the stream holds at least a block -/
  la_af : y.h.la ≤ y.h.lmaf
  la_q : y.h.la ≤ y.h.lmq
  la_x : y.h.la ≤ y.h.lmx
  /-- a column of each of the four matrices holds at least a feature -/
  lt_af : y.h.lt ≤ y.h.lmaf
  lt_ad : y.h.lt ≤ y.h.lmad
  lt_ar : y.h.lt ≤ y.h.lmar
  lt_q : y.h.lt ≤ y.h.lmq
  /-- a block holds more rows than there are positions -/
  lt_la : y.h.lt < y.h.la
  /-- af and ad have a part -/
  NAf0 : y.h.NAf ≠ 0
  NAd0 : y.h.NAd ≠ 0

/-- The first half of the layout. -/
theorem laid2_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : Laid2 y := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨e6, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e21, hy⟩ := ok_of_refuse hy
  obtain ⟨e22, hy⟩ := ok_of_refuse hy
  obtain ⟨e23, hy⟩ := ok_of_refuse hy
  obtain ⟨e24, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  have k6 : h.lt < h.la := Nat.not_le.mp (of_decide_eq_false (or_false_split e6).1)
  have k21 : h.la ≤ h.lmq := Nat.not_lt.mp (of_decide_eq_false e21)
  have k23 : h.la ≤ h.lmaf := Nat.not_lt.mp (of_decide_eq_false e23)
  have k24 : h.la ≤ h.lmx := Nat.not_lt.mp (of_decide_eq_false (or_false_split e24).1)
  have k22 : h.lt ≤ h.lmaf ∧ h.lt ≤ h.lmad ∧ h.lt ≤ h.lmar ∧ h.lt ≤ h.lmq ∧ h.NAf ≠ 0 ∧
      h.NAd ≠ 0 := by
    simp at e22
    omega
  exact {
    T := rfl
    feat := rfl
    kcol := rfl
    mrow := rfl
    parts := rfl
    mxb := rfl
    kxb := rfl
    la_af := k23
    la_q := k21
    la_x := k24
    lt_af := k22.1
    lt_ad := k22.2.1
    lt_ar := k22.2.2.1
    lt_q := k22.2.2.2.1
    lt_la := k6
    NAf0 := k22.2.2.2.2.1
    NAd0 := k22.2.2.2.2.2 }

/-- Every layout that the verifier returns has these facts: the second half of the layout changes
none of the fields that they name. -/
theorem laid2_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : Laid2 y := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have L := laid2_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact {
    T := L.T, feat := L.feat, kcol := L.kcol, mrow := L.mrow, parts := L.parts, mxb := L.mxb,
    kxb := L.kxb, la_af := L.la_af, la_q := L.la_q, la_x := L.la_x, lt_af := L.lt_af,
    lt_ad := L.lt_ad, lt_ar := L.lt_ar, lt_q := L.lt_q, lt_la := L.lt_la, NAf0 := L.NAf0,
    NAd0 := L.NAd0 }

/-! ## The four arrays, member by member -/

/-- layTensors keeps the number of matrices. -/
theorem layTensors_size : ∀ (asks : List (String × ℕ × ℕ × ℕ × ℕ)) (off : Array ℕ),
    (layTensors asks off).2.size = off.size
  | [], _ => rfl
  | (n, mat, nl, cnt, J) :: rest, off => by
    by_cases hnl : nl = 0
    · subst hnl
      exact layTensors_size rest off
    · have hb : (nl == 0) = false := by simpa using hnl
      have e : (layTensors ((n, mat, nl, cnt, J) :: rest) off).2 =
          (layTensors rest (off.modify mat (· + nl * cnt * J))).2 := by
        show (if nl == 0 then _ else _ : List Model.Layer.Ten × Array ℕ).2 = _
        rw [hb]
        rfl
      rw [e, layTensors_size rest, Array.size_modify]

/-- There are four numbers of features in use. -/
theorem offsOf_size (h : Shape) : (offsOf h).size = 4 := layTensors_size _ _

/-- The list of sizes, written out. -/
theorem sizes_four (off : Array ℕ) (hs : off.size = 4) (T l0 l1 l2 l3 n0 n1 n2 n3 : ℕ) :
    ((off.toList.zip [l0, l1, l2, l3]).zip [n0, n1, n2, n3]).map
        (fun x => matrixSizes T x.1.1 x.1.2 x.2) =
      [matrixSizes T (off.getD 0 0) l0 n0, matrixSizes T (off.getD 1 0) l1 n1,
        matrixSizes T (off.getD 2 0) l2 n2, matrixSizes T (off.getD 3 0) l3 n3] := by
  obtain ⟨l⟩ := off
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  all_goals first
    | rfl
    | exact absurd hs (by simp)

/-- The sizes of the four matrices of a shape, written out. -/
theorem sizesOf_eq (h : Shape) :
    sizesOf h =
      [matrixSizes (2 ^ h.lt) ((offsOf h).getD 0 0) h.lmaf h.NAf,
        matrixSizes (2 ^ h.lt) ((offsOf h).getD 1 0) h.lmad h.NAd,
        matrixSizes (2 ^ h.lt) ((offsOf h).getD 2 0) h.lmar 1,
        matrixSizes (2 ^ h.lt) ((offsOf h).getD 3 0) h.lmq 1] :=
  sizes_four _ (offsOf_size h) _ _ _ _ _ _ _ _ _

namespace Laid2

variable {y : Lay} (L : Laid2 y)
include L

/-- The features in use in af. -/
theorem feat0 : y.feat.getD 0 0 = (offsOf y.h).getD 0 0 := by rw [L.feat, sizesOf_eq]; rfl
/-- The features in use in ad. -/
theorem feat1 : y.feat.getD 1 0 = (offsOf y.h).getD 1 0 := by rw [L.feat, sizesOf_eq]; rfl
/-- The features in use in ar. -/
theorem feat2 : y.feat.getD 2 0 = (offsOf y.h).getD 2 0 := by rw [L.feat, sizesOf_eq]; rfl
/-- The features in use in qa. -/
theorem feat3 : y.feat.getD 3 0 = (offsOf y.h).getD 3 0 := by rw [L.feat, sizesOf_eq]; rfl
/-- The rows of a part of af. -/
theorem mrow0 : y.mrow.getD 0 0 = 2 ^ y.h.lmaf := by rw [L.mrow, sizesOf_eq]; rfl
/-- The rows of a part of ad. -/
theorem mrow1 : y.mrow.getD 1 0 = 2 ^ y.h.lmad := by rw [L.mrow, sizesOf_eq]; rfl
/-- The rows of a part of ar. -/
theorem mrow2 : y.mrow.getD 2 0 = 2 ^ y.h.lmar := by rw [L.mrow, sizesOf_eq]; rfl
/-- The rows of a part of qa. -/
theorem mrow3 : y.mrow.getD 3 0 = 2 ^ y.h.lmq := by rw [L.mrow, sizesOf_eq]; rfl
/-- The parts of af. -/
theorem parts0 : y.parts.getD 0 0 = y.h.NAf := by rw [L.parts, sizesOf_eq]; rfl
/-- The parts of ad. -/
theorem parts1 : y.parts.getD 1 0 = y.h.NAd := by rw [L.parts, sizesOf_eq]; rfl
/-- The parts of ar. -/
theorem parts2 : y.parts.getD 2 0 = 1 := by rw [L.parts, sizesOf_eq]; rfl
/-- The parts of qa. -/
theorem parts3 : y.parts.getD 3 0 = 1 := by rw [L.parts, sizesOf_eq]; rfl
/-- The columns of a part of af. -/
theorem kcol0 : y.kcol.getD 0 0 =
    roundUp ((offsOf y.h).getD 0 0) (y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt)) /
      (y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt)) := by rw [L.kcol, sizesOf_eq]; rfl
/-- The columns of a part of ad. -/
theorem kcol1 : y.kcol.getD 1 0 =
    roundUp ((offsOf y.h).getD 1 0) (y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt)) /
      (y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt)) := by rw [L.kcol, sizesOf_eq]; rfl
/-- The columns of a part of ar. -/
theorem kcol2 : y.kcol.getD 2 0 =
    roundUp ((offsOf y.h).getD 2 0) (1 * (2 ^ y.h.lmar / 2 ^ y.h.lt)) /
      (1 * (2 ^ y.h.lmar / 2 ^ y.h.lt)) := by rw [L.kcol, sizesOf_eq]; rfl
/-- The columns of a part of qa. -/
theorem kcol3 : y.kcol.getD 3 0 =
    roundUp ((offsOf y.h).getD 3 0) (1 * (2 ^ y.h.lmq / 2 ^ y.h.lt)) /
      (1 * (2 ^ y.h.lmq / 2 ^ y.h.lt)) := by rw [L.kcol, sizesOf_eq]; rfl

end Laid2

/-! ## The features in use: the verifier's count against the library's -/

/-- The features that the asks of matrix m take together. -/
def totalOf (asks : List (String × ℕ × ℕ × ℕ × ℕ)) (m : ℕ) : ℕ :=
  ((asks.filter fun a => a.2.1 == m).map fun a => a.2.2.1 * a.2.2.2.1 * a.2.2.2.2).sum

/-- The first ask counts if it is of the matrix. -/
theorem totalOf_cons (a : String × ℕ × ℕ × ℕ × ℕ) (rest : List (String × ℕ × ℕ × ℕ × ℕ)) (m : ℕ) :
    totalOf (a :: rest) m =
      (if a.2.1 = m then a.2.2.1 * a.2.2.2.1 * a.2.2.2.2 else 0) + totalOf rest m := by
  unfold totalOf
  by_cases e : a.2.1 = m
  · rw [if_pos e, List.filter_cons_of_pos (by simpa using e), List.map_cons, List.sum_cons]
  · rw [if_neg e, List.filter_cons_of_neg (by simpa using e), Nat.zero_add]

/-- Two lists of asks take what each takes. -/
theorem totalOf_append (l l' : List (String × ℕ × ℕ × ℕ × ℕ)) (m : ℕ) :
    totalOf (l ++ l') m = totalOf l m + totalOf l' m := by
  unfold totalOf
  rw [List.filter_append, List.map_append, List.sum_append]

/-- The features in use that layTensors returns for a matrix: those in use before, plus what the
asks of that matrix take. -/
theorem layTensors_total :
    ∀ (asks : List (String × ℕ × ℕ × ℕ × ℕ)) (off : Array ℕ), (∀ a ∈ asks, a.2.1 < off.size) →
      ∀ m, (layTensors asks off).2.getD m 0 = off.getD m 0 + totalOf asks m
  | [], _, _, _ => rfl
  | (n, mat, nl, cnt, J) :: rest, off, hs, m => by
    have hs' : ∀ a ∈ rest, a.2.1 < off.size := fun a ha => hs a (List.mem_cons_of_mem _ ha)
    rw [totalOf_cons]
    show _ = off.getD m 0 + ((if mat = m then nl * cnt * J else 0) + totalOf rest m)
    by_cases hnl : nl = 0
    · subst hnl
      have e : layTensors ((n, mat, 0, cnt, J) :: rest) off = layTensors rest off := rfl
      rw [e, layTensors_total rest off hs' m]
      split_ifs <;> simp
    · have hb : (nl == 0) = false := by simpa using hnl
      have e : (layTensors ((n, mat, nl, cnt, J) :: rest) off).2 =
          (layTensors rest (off.modify mat (· + nl * cnt * J))).2 := by
        show (if nl == 0 then _ else _ : List Model.Layer.Ten × Array ℕ).2 = _
        rw [hb]
        rfl
      rw [e, layTensors_total rest (off.modify mat (· + nl * cnt * J))
        (fun a ha => by simpa using hs' a ha) m,
        getD_modify_add off mat m _ (hs _ List.mem_cons_self)]
      split_ifs <;> omega

/-- The tensor o, which the list has at profile 4 alone, is of matrix 3. -/
theorem totalOf_tail (h : Shape) (D : Dim) (m : ℕ) (hm : m ≠ 3) :
    totalOf (if h.p4 then [("o", 3, 2, D.nl, D.dq)] else []) m = 0 := by
  by_cases hp : h.p4 = true
  · rw [if_pos hp, totalOf_cons, if_neg (fun e : 3 = m => hm e.symm)]
    rfl
  · rw [if_neg hp]
    rfl

/-- No ask takes nothing. -/
theorem totalOf_nil (m : ℕ) : totalOf [] m = 0 := rfl

/-- Under the switches the verifier's list of tensors takes in af as many features as the library's
list of arrays. -/
theorem total_af (h : Shape) (D : Dim) :
    totalOf (asksRef h D) 0 = Inst.Model.FFSeg.nFeatMx D .af := by
  have r : Inst.Model.FFSeg.nFeatMx D .af =
      1 * D.nl * D.f + (1 * D.nl * D.f + (2 * D.nl * D.f + (2 * D.nl * D.f + (1 * D.nl * D.f + (1
      * D.nl * D.f + (5 * (2 * D.nl - 1) * D.d + (1 * D.nl * D.d + (1 * D.nl * D.d + (2 * D.nl *
      D.d + (2 * D.nl * D.d + (2 * D.nl * D.d + (2 * D.nl * D.d + (2 * D.nl * D.dqk + (2 * D.nl *
      D.dqk + (2 * D.nl * D.dkv + (1 * D.nl * D.dkv + (2 * D.nl * D.f + 0))))))))))))))))) := rfl
  unfold asksRef
  rw [totalOf_append, totalOf_tail h D 0 (by decide), r]
  simp [totalOf_cons, totalOf_nil]

/-- The same in ad. -/
theorem total_ad (h : Shape) (D : Dim) :
    totalOf (asksRef h D) 1 = Inst.Model.FFSeg.nFeatMx D .ad := by
  have r : Inst.Model.FFSeg.nFeatMx D .ad =
      2 * D.nl * D.d + (2 * D.nl * D.d + (2 * D.ne * D.d + 0)) := rfl
  unfold asksRef
  rw [totalOf_append, totalOf_tail h D 1 (by decide), r]
  simp [totalOf_cons, totalOf_nil]

/-- The same in ar. -/
theorem total_ar (h : Shape) (D : Dim) :
    totalOf (asksRef h D) 2 = Inst.Model.FFSeg.nFeatMx D .ar := by
  have r : Inst.Model.FFSeg.nFeatMx D .ar =
      2 * D.ne * D.nx + (1 * D.ne * D.nx + (1 * D.ne * D.nx + (3 * D.ne * 1 + (1 * (2 * D.nl) * 99
      + (2 * D.ne * D.nx + (1 * D.ne * D.nx + 0)))))) := rfl
  unfold asksRef
  rw [totalOf_append, totalOf_tail h D 2 (by decide), r]
  simp [totalOf_cons, totalOf_nil]

/-- The same in qa, at profile 4. -/
theorem total_qa4 (h : Shape) (D : Dim) (hp : h.p4 = true) :
    totalOf (asksRef h D) 3 = Inst.Model.FFSeg.nFeatMx D .qa := by
  have r : Inst.Model.FFSeg.nFeatMx D .qa =
      2 * D.nl * D.dq + (2 * D.nl * D.dkv + (2 * D.nl * D.dkv + (2 * D.nl * D.dq + 0))) := rfl
  unfold asksRef
  rw [if_pos hp, totalOf_append, r]
  simp [totalOf_cons, totalOf_nil]
  ring

/-- At profile 3 the verifier's list has no tensor o: it takes in qa as many features as the
library's arrays before o. -/
theorem total_qa3 (h : Shape) (D : Dim) (hp : h.p4 = false) :
    totalOf (asksRef h D) 3 = Inst.Model.FFSeg.OFF D .o := by
  have r : Inst.Model.FFSeg.OFF D .o =
      2 * D.nl * D.dq + (2 * D.nl * D.dkv + (2 * D.nl * D.dkv + 0)) := rfl
  unfold asksRef
  rw [if_neg (by rw [hp]; decide), List.append_nil, r]
  simp [totalOf_cons, totalOf_nil]

/-- An array has as many features at sizes that agree with the shape as at dimOf. -/
theorem Sized.nFeat_eq {h : Shape} {D : Dim} (Z : Sized h D) :
    Arr.nFeat D = Arr.nFeat (dimOf h) := by
  funext Y
  unfold Arr.nFeat
  rw [Z.cnt_eq, Z.width_eq]

/-- The features in use, under the switches: the verifier's count for each of its matrices is the
library's number of features of the matrix (nFeatMx): for af, ad, ar; for qa at profile 4 (at
profile 3 the verifier has no tensor o, and its count is the library's first feature of o); for the
two matrices of the stream the verifier's xl d. -/
theorem feat_total {y : Lay} (L : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D) :
    y.feat.getD 0 0 = Inst.Model.FFSeg.nFeatMx D .af ∧
    y.feat.getD 1 0 = Inst.Model.FFSeg.nFeatMx D .ad ∧
    y.feat.getD 2 0 = Inst.Model.FFSeg.nFeatMx D .ar ∧
    (y.h.p4 = true → y.feat.getD 3 0 = Inst.Model.FFSeg.nFeatMx D .qa) ∧
    (y.h.p4 = false → y.feat.getD 3 0 = Inst.Model.FFSeg.OFF D .o) ∧
    y.h.xl * y.h.d = Inst.Model.FFSeg.nFeatMx D .xin ∧
    y.h.xl * y.h.d = Inst.Model.FFSeg.nFeatMx D .xout := by
  have eo : ∀ m, (offsOf y.h).getD m 0 = totalOf (asksRef y.h (dimOf y.h)) m := by
    intro m
    unfold offsOf
    rw [tensorAsks_ref _ S, layTensors_total _ _ (asksRef_mat y.h (dimOf y.h)) m]
    have hz : (#[0, 0, 0, 0] : Array ℕ).getD m 0 = 0 := by
      rcases m with _ | _ | _ | _ | m <;> rfl
    rw [hz, Nat.zero_add]
  have en : ∀ μ, Inst.Model.FFSeg.nFeatMx D μ = Inst.Model.FFSeg.nFeatMx (dimOf y.h) μ := by
    intro μ
    unfold Inst.Model.FFSeg.nFeatMx
    rw [Z.nFeat_eq]
  have eO : Inst.Model.FFSeg.OFF D .o = Inst.Model.FFSeg.OFF (dimOf y.h) .o := by
    unfold Inst.Model.FFSeg.OFF
    rw [Z.nFeat_eq]
  have ex : y.h.xl * y.h.d = 5 * 1 * (dimOf y.h).d + 0 := by
    rw [S.xl]
    show 5 * y.h.d = 5 * 1 * y.h.d + 0
    omega
  refine ⟨by rw [L.feat0, eo, total_af, en], by rw [L.feat1, eo, total_ad, en],
    by rw [L.feat2, eo, total_ar, en], fun hp => by rw [L.feat3, eo, total_qa4 _ _ hp, en],
    fun hp => by rw [L.feat3, eo, total_qa3 _ _ hp, eO], ?_, ?_⟩
  · rw [en, ex]
    rfl
  · rw [en, ex]
    rfl

/-! ## Rounding up, in the two texts' forms -/

/-- a / w rounded up is at most n if and only if a is at most n w. -/
theorem ceil_le_iff {a w n : ℕ} (hw : 0 < w) : (a + w - 1) / w ≤ n ↔ a ≤ n * w := by
  have e : (n + 1) * w = n * w + w := by ring
  rw [← Nat.lt_add_one_iff, Nat.div_lt_iff_lt_mul hw, e]
  omega

/-- Rounding up a quotient by c b at once, or first by b and then by c. -/
theorem ceil_ceil (a : ℕ) {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    (a + c * b - 1) / (c * b) = ((a + b - 1) / b + c - 1) / c := by
  refine eq_of_forall_ge_iff fun n => ?_
  rw [ceil_le_iff (Nat.mul_pos hc hb), ceil_le_iff hc, ceil_le_iff hb, Nat.mul_assoc]

/-- The verifier's "x rounded up to a multiple of w, divided by w" is x / w rounded up. -/
theorem roundUp_div (x : ℕ) {w : ℕ} (hw : 0 < w) : roundUp x w / w = (x + w - 1) / w := by
  unfold roundUp
  exact Nat.mul_div_cancel _ hw

/-! ## The second record of sizes -/

/-- The library's sizes of the matrices agree with the verifier's shape. The library has one number
fBig for the features of a column of af, of qa and of the two matrices of the stream, where the
verifier has three (lmaf, lmq, lmx); and it has ad in one part, where the verifier has NAd parts. So
of a shape for which layout returns, where none of the three is below lt (Laid2), this record holds
only if lmaf = lmq = lmx and NAd = 1. -/
structure Sized2 (h : Shape) (D : Dim) : Prop where
  /-- the features of a column of af -/
  fBig_af : D.fBig = h.lmaf - h.lt
  /-- of qa -/
  fBig_q : D.fBig = h.lmq - h.lt
  /-- of a matrix of the stream -/
  fBig_x : D.fBig = h.lmx - h.lt
  /-- of ad -/
  fAd : D.fAd = h.lmad - h.lt
  /-- of ar -/
  fAr : D.fAr = h.lmar - h.lt
  /-- the parts of af -/
  parts : D.parts = h.NAf
  /-- ad is in one part -/
  NAd : h.NAd = 1

section Sizes

variable {y : Lay} (L : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
  (Z2 : Sized2 y.h D)

include L Z in
/-- The positions. -/
theorem T_eq : y.T = D.T := by
  rw [L.T]
  show _ = 2 ^ D.lT
  rw [Z.lT]

include L Z2 in
/-- The features whose cells a column holds: the verifier's rows of a part by its positions, against
the library's 2^lFeat, for the six matrices that hold cells. -/
theorem fcM_eq {μ : Mx} (hμ : μ ≠ .b) :
    fcM y (mxNo μ) = 2 ^ Inst.Model.FFSeg.lFeat D μ := by
  have two : 0 < 2 := by decide
  have hx : y.h.lt ≤ y.h.lmx := Nat.le_trans (Nat.le_of_lt L.lt_la) L.la_x
  cases μ with
  | b => exact absurd rfl hμ
  | af =>
    show y.mrow.getD 0 0 / y.T = 2 ^ D.fBig
    rw [L.mrow0, L.T, Z2.fBig_af, Nat.pow_div L.lt_af two]
  | ad =>
    show y.mrow.getD 1 0 / y.T = 2 ^ D.fAd
    rw [L.mrow1, L.T, Z2.fAd, Nat.pow_div L.lt_ad two]
  | ar =>
    show y.mrow.getD 2 0 / y.T = 2 ^ D.fAr
    rw [L.mrow2, L.T, Z2.fAr, Nat.pow_div L.lt_ar two]
  | qa =>
    show y.mrow.getD 3 0 / y.T = 2 ^ D.fBig
    rw [L.mrow3, L.T, Z2.fBig_q, Nat.pow_div L.lt_q two]
  | xin =>
    show y.mxb / y.T = 2 ^ D.fBig
    rw [L.mxb, L.T, Z2.fBig_x, Nat.pow_div hx two]
  | xout =>
    show y.mxb / y.T = 2 ^ D.fBig
    rw [L.mxb, L.T, Z2.fBig_x, Nat.pow_div hx two]

include L S Z Z2 in
/-- The columns of a part of af: the verifier's number (matrixSizes in
OnBytes/Model/LayerLayout.lean: the features in use, rounded up to a multiple of parts times the
features of a column, by that product) is the library's afCols (rounded up to whole columns, then to
parts of equal size). -/
theorem afCols_eq : colsM y 0 = Inst.Model.FFSeg.afCols D := by
  have two : 0 < 2 := by decide
  have hp : 0 < y.h.NAf := Nat.pos_of_ne_zero L.NAf0
  have hf : 0 < 2 ^ D.fBig := Nat.two_pow_pos _
  show y.kcol.getD 0 0 = _
  unfold Inst.Model.FFSeg.afCols
  rw [L.kcol0, ← L.feat0, (feat_total L S Z).1, Nat.pow_div L.lt_af two, ← Z2.fBig_af,
    roundUp_div _ (Nat.mul_pos hp hf), ceil_ceil _ hf hp, Z2.parts]

include L Z2 in
/-- The columns of the five matrices in one part: the features in use by the features of a column,
rounded up. -/
theorem colsM_one :
    colsM y 1 = (y.feat.getD 1 0 + 2 ^ D.fAd - 1) / 2 ^ D.fAd ∧
    colsM y 2 = (y.feat.getD 2 0 + 2 ^ D.fAr - 1) / 2 ^ D.fAr ∧
    colsM y 3 = (y.feat.getD 3 0 + 2 ^ D.fBig - 1) / 2 ^ D.fBig ∧
    colsM y 4 = (y.h.xl * y.h.d + 2 ^ D.fBig - 1) / 2 ^ D.fBig ∧
    colsM y 5 = (y.h.xl * y.h.d + 2 ^ D.fBig - 1) / 2 ^ D.fBig := by
  have two : 0 < 2 := by decide
  have hx : y.h.lt ≤ y.h.lmx := Nat.le_trans (Nat.le_of_lt L.lt_la) L.la_x
  have ex : y.kxb = (y.h.xl * y.h.d + 2 ^ D.fBig - 1) / 2 ^ D.fBig := by
    rw [L.kxb, Nat.pow_div hx two, ← Z2.fBig_x, roundUp_div _ (Nat.two_pow_pos _)]
  refine ⟨?_, ?_, ?_, ex, ex⟩
  · show y.kcol.getD 1 0 = _
    rw [L.kcol1, ← L.feat1, Z2.NAd, Nat.one_mul, Nat.pow_div L.lt_ad two, ← Z2.fAd,
      roundUp_div _ (Nat.two_pow_pos _)]
  · show y.kcol.getD 2 0 = _
    rw [L.kcol2, ← L.feat2, Nat.one_mul, Nat.pow_div L.lt_ar two, ← Z2.fAr,
      roundUp_div _ (Nat.two_pow_pos _)]
  · show y.kcol.getD 3 0 = _
    rw [L.kcol3, ← L.feat3, Nat.one_mul, Nat.pow_div L.lt_q two, ← Z2.fBig_q,
      roundUp_div _ (Nat.two_pow_pos _)]

end Sizes

/-! ## The verifier's rule is the library's address -/

/-- The entry of the verifier's matrices at an address of the library: matrix, row, column. A column
of af is looked up in its part by the library's own rule afPart; each other matrix is the one part
that the verifier's list has for it. Which number of the list stands for which of the library's
matrices is said here, by firstM and mxNo. The matrix b is not meant: no cell's address names it. -/
def atAddr {K : Type} (y : Lay) (D : Dim) (M : Mats K) : Mx × ℕ × ℕ → K := fun p =>
  if p.1 = .af then
    M (firstM y 0 + (Inst.Model.FFSeg.afPart D p.2.2).1) p.2.1 (Inst.Model.FFSeg.afPart D p.2.2).2
  else M (firstM y (mxNo p.1)) p.2.1 p.2.2

/-- atAddr in af. -/
theorem atAddr_af {K : Type} (y : Lay) (D : Dim) (M : Mats K) (row col : ℕ) :
    atAddr y D M (.af, row, col) =
      M (firstM y 0 + col / Inst.Model.FFSeg.afCols D) row (col % Inst.Model.FFSeg.afCols D) := by
  unfold atAddr
  exact if_pos rfl

/-- atAddr in another matrix. -/
theorem atAddr_ne {K : Type} (y : Lay) (D : Dim) (M : Mats K) {μ : Mx} (h : μ ≠ .af)
    (row col : ℕ) : atAddr y D M (μ, row, col) = M (firstM y (mxNo μ)) row col := by
  unfold atAddr
  exact if_neg h

/-- In the library's order the arrays q, kx, v of the matrix qa end before o begins. -/
theorem before_o (D : Dim) {X : Arr} (hm : X.mx = .qa) (hne : X ≠ .o) :
    Inst.Model.FFSeg.OFF D X + X.nFeat D ≤ Inst.Model.FFSeg.OFF D .o := by
  have e0 : Inst.Model.FFSeg.OFF D .o =
      Arr.nFeat D .q + (Arr.nFeat D .kx + (Arr.nFeat D .v + 0)) := rfl
  have e1 : Inst.Model.FFSeg.OFF D .q = 0 := rfl
  have e2 : Inst.Model.FFSeg.OFF D .kx = Arr.nFeat D .q + 0 := rfl
  have e3 : Inst.Model.FFSeg.OFF D .v = Arr.nFeat D .q + (Arr.nFeat D .kx + 0) := rfl
  cases X
  all_goals first
    | exact absurd hm (by decide)
    | exact absurd rfl hne
    | (rw [e0, e1]; omega)
    | (rw [e0, e2]; omega)
    | (rw [e0, e3]; omega)

section Address

variable {y : Lay} (L : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
  (Z2 : Sized2 y.h D)

include L S Z Z2 in
/-- A valid cell of a matrix in one part lies in a column that the verifier's matrix has. The
attention output o is asked for at profile 4 alone: at profile 3 the verifier's qa ends before
it. -/
theorem col_lt_cols {X : Arr} {k inst j : ℕ} (hk : k < X.nCell) (hi : inst < X.cnt D)
    (hj : j < X.width D) (ho : X = .o → y.h.p4 = true) (ha : X.mx ≠ .af) :
    Inst.Model.FFSeg.feat D X k inst j / 2 ^ Inst.Model.FFSeg.lFeat D X.mx <
      colsM y (mxNo X.mx) := by
  have hφ := Inst.Model.FFSeg.IndexFacts.feat_lt D hk hi hj
  have hin := (Inst.Model.FFSeg.IndexFacts.feat_in D hk hi hj).2
  obtain ⟨-, f1, f2, f3, f3', f4, f5⟩ := feat_total L S Z
  obtain ⟨c1, c2, c3, c4, c5⟩ := colsM_one L Z2
  generalize Inst.Model.FFSeg.feat D X k inst j = φ at hφ hin ⊢
  cases hμ : X.mx with
  | af => exact absurd hμ ha
  | b => exact absurd hμ (Inst.Model.FFSeg.IndexFacts.mx_ne_b X)
  | ad =>
    rw [hμ] at hφ
    show φ / 2 ^ D.fAd < colsM y 1
    rw [c1, f1]
    exact Inst.Model.FFSeg.IndexFacts.div_lt_ceil (Nat.two_pow_pos _) hφ
  | ar =>
    rw [hμ] at hφ
    show φ / 2 ^ D.fAr < colsM y 2
    rw [c2, f2]
    exact Inst.Model.FFSeg.IndexFacts.div_lt_ceil (Nat.two_pow_pos _) hφ
  | qa =>
    rw [hμ] at hφ
    show φ / 2 ^ D.fBig < colsM y 3
    rw [c3]
    refine Inst.Model.FFSeg.IndexFacts.div_lt_ceil (Nat.two_pow_pos _) ?_
    by_cases hp : y.h.p4 = true
    · rw [f3 hp]
      exact hφ
    · have hp' : y.h.p4 = false := by simpa using hp
      rw [f3' hp']
      exact Nat.lt_of_lt_of_le hin (before_o D hμ fun e => hp (ho e))
  | xin =>
    rw [hμ] at hφ
    show φ / 2 ^ D.fBig < colsM y 4
    rw [c4, f4]
    exact Inst.Model.FFSeg.IndexFacts.div_lt_ceil (Nat.two_pow_pos _) hφ
  | xout =>
    rw [hμ] at hφ
    show φ / 2 ^ D.fBig < colsM y 5
    rw [c5, f5]
    exact Inst.Model.FFSeg.IndexFacts.div_lt_ceil (Nat.two_pow_pos _) hφ

include L S Z Z2 in
/-- The verifier's rule is the library's address. The cells cellsAt y M are read in the entries M of
the verifier's matrices by the rule that its tables of reads follow; cellsOf gives them the
library's names. For every valid name q (the array o at profile 4 alone) that cell is the entry of
M at the library's own address addr D q: in af the same part, the same row, the same column. That it
is the same matrix holds by the definition of atAddr, which pairs the two lists of matrices. -/
theorem cells_addr {K : Type} (M : Mats K) (q : Cell) (hv : q.Valid D)
    (ho : q.X = .o → y.h.p4 = true) :
    cellsOf D (cellsAt y M) q = atAddr y D M (Inst.Model.FFSeg.addr D q) := by
  obtain ⟨hk, hi, hj, -⟩ := hv
  have hfc := fcM_eq L Z2 (D := D) (Inst.Model.FFSeg.IndexFacts.mx_ne_b q.X)
  have hT := T_eq L Z
  show M (firstM y (mxNo q.X.mx) +
        Inst.Model.FFSeg.feat D q.X q.k q.inst q.j / fcM y (mxNo q.X.mx) / colsM y (mxNo q.X.mx))
      (Inst.Model.FFSeg.feat D q.X q.k q.inst q.j % fcM y (mxNo q.X.mx) * y.T + q.i)
      (Inst.Model.FFSeg.feat D q.X q.k q.inst q.j / fcM y (mxNo q.X.mx) % colsM y (mxNo q.X.mx)) =
    atAddr y D M (q.X.mx,
      Inst.Model.FFSeg.feat D q.X q.k q.inst q.j % 2 ^ Inst.Model.FFSeg.lFeat D q.X.mx * D.T + q.i,
      Inst.Model.FFSeg.feat D q.X q.k q.inst q.j / 2 ^ Inst.Model.FFSeg.lFeat D q.X.mx)
  rw [hfc, hT]
  by_cases ha : q.X.mx = .af
  · have hc := afCols_eq L S Z Z2
    generalize Inst.Model.FFSeg.feat D q.X q.k q.inst q.j = φ
    rw [ha, atAddr_af]
    show M (firstM y 0 + _ / colsM y 0) _ (_ % colsM y 0) = _
    rw [hc]
  · have hc := col_lt_cols L S Z Z2 hk hi hj ho ha
    rw [atAddr_ne y D M ha, Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc, Nat.add_zero]

end Address

/-- cells_addr for the layout that layout returns. -/
theorem cells_addr_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) {D : Dim} (Z : Sized h D) (Z2 : Sized2 h D)
    {K : Type} (M : Mats K) (q : Cell) (hv : q.Valid D) (ho : q.X = .o → h.p4 = true) :
    cellsOf D (cellsAt y M) q = atAddr y D M (Inst.Model.FFSeg.addr D q) := by
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  exact cells_addr (laid2_of_layout hy) S Z Z2 M q hv ho

/-! ## The sizes of the matrices -/

section Sizes2

variable {y : Lay} (L : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
  (Z2 : Sized2 y.h D)

include L Z Z2 in
/-- The rows of a part are the library's 2^lRow, for the six matrices that hold cells. -/
theorem rowsM_eq {μ : Mx} (hμ : μ ≠ .b) :
    rowsM y (mxNo μ) = 2 ^ Inst.Model.FFSeg.lRow D μ := by
  have hx : y.h.lt ≤ y.h.lmx := Nat.le_trans (Nat.le_of_lt L.lt_la) L.la_x
  cases μ with
  | b => exact absurd rfl hμ
  | af =>
    show y.mrow.getD 0 0 = 2 ^ (D.fBig + D.lT)
    rw [L.mrow0, Z2.fBig_af, Z.lT, Nat.sub_add_cancel L.lt_af]
  | ad =>
    show y.mrow.getD 1 0 = 2 ^ (D.fAd + D.lT)
    rw [L.mrow1, Z2.fAd, Z.lT, Nat.sub_add_cancel L.lt_ad]
  | ar =>
    show y.mrow.getD 2 0 = 2 ^ (D.fAr + D.lT)
    rw [L.mrow2, Z2.fAr, Z.lT, Nat.sub_add_cancel L.lt_ar]
  | qa =>
    show y.mrow.getD 3 0 = 2 ^ (D.fBig + D.lT)
    rw [L.mrow3, Z2.fBig_q, Z.lT, Nat.sub_add_cancel L.lt_q]
  | xin =>
    show y.mxb = 2 ^ (D.fBig + D.lT)
    rw [L.mxb, Z2.fBig_x, Z.lT, Nat.sub_add_cancel hx]
  | xout =>
    show y.mxb = 2 ^ (D.fBig + D.lT)
    rw [L.mxb, Z2.fBig_x, Z.lT, Nat.sub_add_cancel hx]

include L S Z Z2 in
/-- The columns are the library's nCol: for af those of all parts together; for qa at profile 4. -/
theorem nCol_eq :
    partsM y 0 * colsM y 0 = Inst.Model.FFSeg.nCol D .af ∧
    colsM y 1 = Inst.Model.FFSeg.nCol D .ad ∧ colsM y 2 = Inst.Model.FFSeg.nCol D .ar ∧
    (y.h.p4 = true → colsM y 3 = Inst.Model.FFSeg.nCol D .qa) ∧
    colsM y 4 = Inst.Model.FFSeg.nCol D .xin ∧ colsM y 5 = Inst.Model.FFSeg.nCol D .xout := by
  obtain ⟨-, f1, f2, f3, -, f4, f5⟩ := feat_total L S Z
  obtain ⟨c1, c2, c3, c4, c5⟩ := colsM_one L Z2
  refine ⟨?_, by rw [c1, f1]; rfl, by rw [c2, f2]; rfl, fun hp => by rw [c3, f3 hp]; rfl,
    by rw [c4, f4]; rfl, by rw [c5, f5]; rfl⟩
  show y.parts.getD 0 0 * colsM y 0 = D.parts * Inst.Model.FFSeg.afCols D
  rw [L.parts0, afCols_eq L S Z Z2, Z2.parts]

include L Z Z2 in
/-- The rows of all parts of the six matrices, and 2^lmb rows for the matrix b, are together the
library's mZ, if the library's r is the verifier's lmb. The left side is written with the numbers of
the layout: it is not compared here with the list of matrices of a sub-proof's plan. -/
theorem mZ_eq (hr : D.r = y.h.lmb) :
    partsM y 0 * rowsM y 0 +
        (rowsM y 1 + rowsM y 2 + 2 ^ y.h.lmb + rowsM y 3 + rowsM y 4 + rowsM y 5) =
      Inst.Model.FFSeg.mZ D := by
  have r0 := rowsM_eq L Z Z2 (μ := .af) (by decide)
  have r1 := rowsM_eq L Z Z2 (μ := .ad) (by decide)
  have r2 := rowsM_eq L Z Z2 (μ := .ar) (by decide)
  have r3 := rowsM_eq L Z Z2 (μ := .qa) (by decide)
  have r4 := rowsM_eq L Z Z2 (μ := .xin) (by decide)
  have r5 := rowsM_eq L Z Z2 (μ := .xout) (by decide)
  have p0 : partsM y 0 = D.parts := by
    show y.parts.getD 0 0 = _
    rw [L.parts0, Z2.parts]
  have rb : 2 ^ y.h.lmb = 2 ^ Inst.Model.FFSeg.lRow D .b := by
    show _ = 2 ^ D.r
    rw [hr]
  have e : Inst.Model.FFSeg.mZ D = D.parts * 2 ^ Inst.Model.FFSeg.lRow D .af +
      (2 ^ Inst.Model.FFSeg.lRow D .ad + (2 ^ Inst.Model.FFSeg.lRow D .ar +
        (2 ^ Inst.Model.FFSeg.lRow D .b + (2 ^ Inst.Model.FFSeg.lRow D .qa +
          (2 ^ Inst.Model.FFSeg.lRow D .xin + (2 ^ Inst.Model.FFSeg.lRow D .xout + 0)))))) := rfl
  have r0' : rowsM y 0 = 2 ^ Inst.Model.FFSeg.lRow D .af := r0
  have r1' : rowsM y 1 = 2 ^ Inst.Model.FFSeg.lRow D .ad := r1
  have r2' : rowsM y 2 = 2 ^ Inst.Model.FFSeg.lRow D .ar := r2
  have r3' : rowsM y 3 = 2 ^ Inst.Model.FFSeg.lRow D .qa := r3
  have r4' : rowsM y 4 = 2 ^ Inst.Model.FFSeg.lRow D .xin := r4
  have r5' : rowsM y 5 = 2 ^ Inst.Model.FFSeg.lRow D .xout := r5
  rw [e, p0, r0', r1', r2', r3', r4', r5', rb]
  ring

end Sizes2

/-! ## Sizes that meet both records -/

/-- Sizes of the library for a shape: those of dimOf, with the numbers that the library's addresses
read taken from the shape: the features of a column of af, qa and the stream from the height of af,
those of ad and of ar from their heights, and the parts of af. -/
def dimA (h : Shape) : Dim :=
  { dimOf h with
    fBig := h.lmaf - h.lt, fAd := h.lmad - h.lt, fAr := h.lmar - h.lt, parts := h.NAf }

/-- The two records of sizes can be met together, by every shape in which af, qa and the stream have
columns of one height and ad is in one part. -/
theorem sized_dimA {h : Shape} (hq : h.lmq = h.lmaf) (hx : h.lmx = h.lmaf) (hd : h.NAd = 1) :
    Sized h (dimA h) ∧ Sized2 h (dimA h) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, by rw [hq]; rfl, by rw [hx]; rfl, rfl, rfl, rfl, hd⟩⟩

/-! ## Inside and apart -/

/-- Where the cell with the library's name q stands in the verifier's matrices, by the rule of
cellsAt: the matrix's number in the sub-proof's list, the row, the column. -/
def placeOf (y : Lay) (D : Dim) (q : Cell) : ℕ × ℕ × ℕ :=
  (firstM y (mxNo q.X.mx) +
      Inst.Model.FFSeg.feat D q.X q.k q.inst q.j / fcM y (mxNo q.X.mx) / colsM y (mxNo q.X.mx),
    Inst.Model.FFSeg.feat D q.X q.k q.inst q.j % fcM y (mxNo q.X.mx) * y.T + q.i,
    Inst.Model.FFSeg.feat D q.X q.k q.inst q.j / fcM y (mxNo q.X.mx) % colsM y (mxNo q.X.mx))

/-- The cell is the entry at that place. -/
theorem cells_place {K : Type} (y : Lay) (D : Dim) (M : Mats K) (q : Cell) :
    cellsOf D (cellsAt y M) q = M (placeOf y D q).1 (placeOf y D q).2.1 (placeOf y D q).2.2 := rfl

/-- The columns of all parts of af hold its features. This is the library's col_lt for af, which
reads of Dim.OK only that there is a part. -/
theorem af_col_lt (D : Dim) (hp : 0 < D.parts) {φ : ℕ}
    (h : φ < Inst.Model.FFSeg.nFeatMx D .af) :
    φ / 2 ^ D.fBig < Inst.Model.FFSeg.afCols D * D.parts := by
  have hc := Inst.Model.FFSeg.IndexFacts.div_lt_ceil (Nat.two_pow_pos D.fBig) h
  unfold Inst.Model.FFSeg.afCols
  have := Nat.lt_div_mul_add
    (a := (Inst.Model.FFSeg.nFeatMx D .af + 2 ^ D.fBig - 1) / 2 ^ D.fBig + D.parts - 1) hp
  omega

/-- Two valid names of cells in one matrix with one feature are one array, limb, instance and
channel. This is a part of the library's proof of addrInj, which does not read Dim.OK. -/
theorem feat_inj (D : Dim) {X X' : Arr} {k k' inst inst' j j' : ℕ} (hk : k < X.nCell)
    (hi : inst < X.cnt D) (hj : j < X.width D) (hk' : k' < X'.nCell) (hi' : inst' < X'.cnt D)
    (hj' : j' < X'.width D) (hm : X.mx = X'.mx)
    (hφ : Inst.Model.FFSeg.feat D X k inst j = Inst.Model.FFSeg.feat D X' k' inst' j') :
    X = X' ∧ k = k' ∧ inst = inst' ∧ j = j' := by
  have hX : X = X' := by
    by_contra hne
    have a1 := Inst.Model.FFSeg.IndexFacts.feat_in D hk hi hj
    have a2 := Inst.Model.FFSeg.IndexFacts.feat_in D hk' hi' hj'
    have hmem : X' ∈ Inst.Model.FFSeg.arrs X.mx := hm ▸ Inst.Model.FFSeg.IndexFacts.mem_arrs X'
    have e2 : Inst.Model.FFSeg.OFF D X' =
        Inst.Model.FFSeg.IndexFacts.offL (Arr.nFeat D) (Inst.Model.FFSeg.arrs X.mx) X' := by
      rw [Inst.Model.FFSeg.IndexFacts.OFF_eq, hm]
    rcases Inst.Model.FFSeg.IndexFacts.offL_disj (Arr.nFeat D)
      (Inst.Model.FFSeg.IndexFacts.mem_arrs X) hmem hne with h1 | h1
    · rw [← Inst.Model.FFSeg.IndexFacts.OFF_eq, ← e2] at h1
      omega
    · rw [← Inst.Model.FFSeg.IndexFacts.OFF_eq, ← e2] at h1
      omega
  subst hX
  unfold Inst.Model.FFSeg.feat at hφ
  obtain ⟨h1, h2⟩ := Inst.Model.FFSeg.IndexFacts.mr_inj hj hj'
    (Nat.add_left_cancel (by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact hφ))
  obtain ⟨h3, h4⟩ := Inst.Model.FFSeg.IndexFacts.mr_inj hi hi' h1
  exact ⟨rfl, h3, h4, h2⟩

/-- In the sub-proof's list the parts of two of the six matrices share no number. -/
theorem mx_of_number (y : Lay) {μ μ' : Mx} (hμ : μ ≠ .b) (hμ' : μ' ≠ .b) {n : ℕ}
    (h1 : firstM y (mxNo μ) ≤ n ∧ n < firstM y (mxNo μ) + partsM y (mxNo μ))
    (h2 : firstM y (mxNo μ') ≤ n ∧ n < firstM y (mxNo μ') + partsM y (mxNo μ')) : μ = μ' := by
  have F0 : firstM y 0 = 0 := rfl
  have F1 : firstM y 1 = y.parts.getD 0 0 := rfl
  have F2 : firstM y 2 = y.parts.getD 0 0 + y.parts.getD 1 0 := rfl
  have F3 : firstM y 3 = y.parts.getD 0 0 + y.parts.getD 1 0 + 2 := rfl
  have F4 : firstM y 4 = y.parts.getD 0 0 + y.parts.getD 1 0 + 4 := rfl
  have F5 : firstM y 5 = y.parts.getD 0 0 + y.parts.getD 1 0 + 3 := rfl
  have P0 : partsM y 0 = y.parts.getD 0 0 := rfl
  have P1 : partsM y 1 = y.parts.getD 1 0 := rfl
  have P2 : partsM y 2 = 1 := rfl
  have P3 : partsM y 3 = 1 := rfl
  have P4 : partsM y 4 = 1 := rfl
  have P5 : partsM y 5 = 1 := rfl
  cases μ <;> cases μ' <;> simp only [mxNo] at h1 h2 <;> first
    | rfl
    | exact absurd rfl hμ
    | exact absurd rfl hμ'
    | (exfalso; omega)

section Apart

variable {y : Lay} (L : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
  (Z2 : Sized2 y.h D)

include L S Z Z2 in
/-- A valid cell stands inside the verifier's matrices: in one of the parts that the list has for
its matrix, in a row and in a column that a part has. -/
theorem place_inside (q : Cell) (hv : q.Valid D) (ho : q.X = .o → y.h.p4 = true) :
    firstM y (mxNo q.X.mx) ≤ (placeOf y D q).1 ∧
      (placeOf y D q).1 < firstM y (mxNo q.X.mx) + partsM y (mxNo q.X.mx) ∧
      (placeOf y D q).2.1 < rowsM y (mxNo q.X.mx) ∧
      (placeOf y D q).2.2 < colsM y (mxNo q.X.mx) := by
  obtain ⟨hk, hi, hj, hp⟩ := hv
  have hb := Inst.Model.FFSeg.IndexFacts.mx_ne_b q.X
  have hfc := fcM_eq L Z2 (D := D) hb
  have hT := T_eq L Z
  have hrow : Inst.Model.FFSeg.feat D q.X q.k q.inst q.j % fcM y (mxNo q.X.mx) * y.T + q.i <
      rowsM y (mxNo q.X.mx) := by
    rw [rowsM_eq L Z Z2 hb, Inst.Model.FFSeg.IndexFacts.lRow_eq D hb, pow_add, hfc, hT]
    exact Inst.Model.FFSeg.IndexFacts.mr_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) hp
  refine ⟨Nat.le_add_right _ _, ?_, hrow, ?_⟩
  · show firstM y (mxNo q.X.mx) + _ / fcM y (mxNo q.X.mx) / colsM y (mxNo q.X.mx) < _
    refine Nat.add_lt_add_left ?_ _
    rw [hfc]
    by_cases ha : q.X.mx = .af
    · have hφ := Inst.Model.FFSeg.IndexFacts.feat_lt D hk hi hj
      generalize Inst.Model.FFSeg.feat D q.X q.k q.inst q.j = φ at hφ ⊢
      rw [ha] at hφ ⊢
      show φ / 2 ^ D.fBig / colsM y 0 < y.parts.getD 0 0
      rw [afCols_eq L S Z Z2, L.parts0, ← Z2.parts]
      exact Nat.div_lt_of_lt_mul
        (af_col_lt D (by rw [Z2.parts]; exact Nat.pos_of_ne_zero L.NAf0) hφ)
    · have hc := col_lt_cols L S Z Z2 hk hi hj ho ha
      rw [Nat.div_eq_of_lt hc]
      have h1 : partsM y (mxNo q.X.mx) = 1 := by
        have P1 : partsM y 1 = 1 := by
          show y.parts.getD 1 0 = 1
          rw [L.parts1, Z2.NAd]
        cases hμ : q.X.mx with
        | af => exact absurd hμ ha
        | b => exact absurd hμ hb
        | ad => exact P1
        | ar => rfl
        | qa => rfl
        | xin => rfl
        | xout => rfl
      rw [h1]
      exact Nat.one_pos
  · show _ / fcM y (mxNo q.X.mx) % colsM y (mxNo q.X.mx) < _
    refine Nat.mod_lt _ ?_
    by_cases ha : q.X.mx = .af
    · have hφ := Inst.Model.FFSeg.IndexFacts.feat_lt D hk hi hj
      rw [ha] at hφ ⊢
      show 0 < colsM y 0
      rw [afCols_eq L S Z Z2]
      have h2 := af_col_lt D (by rw [Z2.parts]; exact Nat.pos_of_ne_zero L.NAf0) hφ
      exact Nat.pos_of_ne_zero fun e => by
        rw [e, Nat.zero_mul] at h2
        exact Nat.not_lt_zero _ h2
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (col_lt_cols L S Z Z2 hk hi hj ho ha)

include L S Z Z2 in
/-- Two valid cells do not stand at one place of the verifier's matrices. -/
theorem place_apart (q q' : Cell) (hv : q.Valid D) (hv' : q'.Valid D)
    (ho : q.X = .o → y.h.p4 = true) (ho' : q'.X = .o → y.h.p4 = true)
    (h : placeOf y D q = placeOf y D q') : q = q' := by
  obtain ⟨i1, i2, -, -⟩ := place_inside L S Z Z2 q hv ho
  obtain ⟨i1', i2', -, -⟩ := place_inside L S Z Z2 q' hv' ho'
  rw [← h] at i1' i2'
  have hm : q.X.mx = q'.X.mx := mx_of_number y (Inst.Model.FFSeg.IndexFacts.mx_ne_b q.X)
    (Inst.Model.FFSeg.IndexFacts.mx_ne_b q'.X) ⟨i1, i2⟩ ⟨i1', i2'⟩
  obtain ⟨hk, hi, hj, hp⟩ := hv
  obtain ⟨hk', hi', hj', hp'⟩ := hv'
  obtain ⟨X, k, inst, j, i⟩ := q
  obtain ⟨X', k', inst', j', i'⟩ := q'
  simp only at hk hi hj hp hk' hi' hj' hp' hm
  unfold placeOf at h
  simp only at h
  rw [← hm] at h
  obtain ⟨a1, h'⟩ := Prod.mk.inj h
  obtain ⟨a2, a3⟩ := Prod.mk.inj h'
  have a1' := Nat.add_left_cancel a1
  rw [T_eq L Z] at a2
  obtain ⟨b1, b2⟩ := Inst.Model.FFSeg.IndexFacts.mr_inj hp hp' a2
  have b3 : Inst.Model.FFSeg.feat D X k inst j / fcM y (mxNo X.mx) =
      Inst.Model.FFSeg.feat D X' k' inst' j' / fcM y (mxNo X.mx) := by
    rw [← Nat.div_add_mod (Inst.Model.FFSeg.feat D X k inst j / fcM y (mxNo X.mx))
      (colsM y (mxNo X.mx)), a1', a3, Nat.div_add_mod]
  have hφ : Inst.Model.FFSeg.feat D X k inst j = Inst.Model.FFSeg.feat D X' k' inst' j' := by
    rw [← Nat.div_add_mod (Inst.Model.FFSeg.feat D X k inst j) (fcM y (mxNo X.mx)), b3, b1,
      Nat.div_add_mod]
  obtain ⟨e1, e2, e3, e4⟩ := feat_inj D hk hi hj hk' hi' hj' hm hφ
  subst e1 e2 e3 e4 b2
  rfl

end Apart

#print axioms laid2_of_layout
#print axioms feat_total
#print axioms afCols_eq
#print axioms colsM_one
#print axioms cells_addr
#print axioms cells_addr_of_layout
#print axioms rowsM_eq
#print axioms nCol_eq
#print axioms mZ_eq
#print axioms sized_dimA
#print axioms place_inside
#print axioms place_apart

end OnBytes.Road
