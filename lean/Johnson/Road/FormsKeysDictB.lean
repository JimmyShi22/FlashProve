-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysDictB.lean: the dictionary of cells of a feed-forward segment, backwards: the
verifier's list of matrices for one group, filled from the library's family of matrices.

Johnson/Road/FormsKeysDict.lean and Johnson/Road/FormsKeysDictZ.lean fill the library's matrices
from the verifier's. This file goes the other way. It serves to show that a statement on the
verifier's matrices can be met: a family of matrices that meets the library's conditions, such as
that of the library's honest trace, gives a list of matrices for each group in which the verifier's
rule reads the same cells.

What is compared with what: the library's reading tM (Cm/TargetSegFFAffPass.lean) of ANY family of
integer matrices against cellsOf and cellsAt (Johnson/Road/FormsKeysFits.lean,
Johnson/Road/FormsKeysMat.lean) at matrices of this file; the library's InShape (Cm/SegLayout.lean)
against SmallM of FormsKeysDictZ.lean.

Main definitions, both of this file.
 - slotOf: the slot that a number of the verifier's list fills; 8 for the matrix b and every other
   number.
 - backM y g A: entry n of the list is slot slotOf y n of segment 2 g of A; but the stream that
   comes into a later group is slot 7 of segment 2 g - 2, where the library has it. 0 from row
   65,536 and from column 5,990 on, and in the matrix b.
Main theorems.
 - slotOf_portNo: slotOf undoes portNo on the eight slots.
 - lib_back: at every place that libMZ keeps, in a column below 5,990, libM of backM is A.
 - dict_back: tM g A is, at every valid name, the cell that the verifier's rule reads in
   backM y g A.
 - small_back: if A is below 2^18 in absolute value at all places of the library's shapes, the
   matrices backM y g A meet SmallM, for g < 12.

The hypotheses. dict_back: those of dict_valid (FormsKeysDict.lean, whose head says where they are
met: at the full-size example alone). small_back: the layout, the switches, the matrices' sizes; and
the bound on A. The family that is 0 meets it. By the clause admit of the laws of the library's
partition (Cb/Part/LdPartDef.lean, with B := 129 in Cm/TargetPart.lean; the statement read, not used
here) the matrices of a witness of the library's relation are below 129 at all places of that
partition's shapes. Johnson/Road/FormsKeysRunDB.lean runs dict_back's conclusion at the full-size
example's layout.

Which value is which: the entries of A are hidden values; here they are any integers.

What is not claimed. That the matrices backM y g A of neighbouring groups are one matrix where the
verifier's plan gives them one label: the stream that goes out of group g - 1 and the stream that
comes into group g are both slot 7 of segment 2 g - 2, so they are equal below row 65,536 and column
5,990; no theorem here says so. Which number of the list is which matrix (see FormsKeysDict.lean).
Nothing on attention or the head. The program does not import this file.
-/
import Johnson.Road.FormsKeysDictZ

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Lay layout matIx)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Cell)
open Cm.Seg (at' plFF ownFF)

/-! ## The definitions -/

/-- The slot that number n of the verifier's list of matrices fills; 8 if it fills none. -/
def slotOf (y : Lay) (n : ℕ) : ℕ :=
  if n = firstM y 1 then 3
  else if n = firstM y 2 then 4
  else if n = firstM y 3 then 5
  else if n = firstM y 4 then 6
  else if n = firstM y 5 then 7
  else if firstM y 0 ≤ n ∧ n < firstM y 0 + 3 then n - firstM y 0
  else 8

/-- The verifier's list of matrices for group g, filled from the library's family A. -/
def backM (y : Lay) (g : ℕ) (A : ℕ → ℕ → ℕ → ℤ) : Mats ℤ := fun n r c =>
  if slotOf y n < 8 ∧ r < 65536 ∧ c < 5990 then
    (if slotOf y n = 6 ∧ 0 < g then A (2 * g - 2) (7 * 65536 + r) c
      else A (2 * g) (slotOf y n * 65536 + r) c)
  else 0

/-! ## The numbers of the list -/

/-- With three parts of af and one of ad, the first numbers of the six matrices in the list. -/
theorem firstM_ref (y : Lay) (h3 : y.parts.getD 0 0 = 3) (h1 : y.parts.getD 1 0 = 1) :
    firstM y 0 = 0 ∧ firstM y 1 = 3 ∧ firstM y 2 = 4 ∧ firstM y 3 = 6 ∧ firstM y 4 = 8 ∧
      firstM y 5 = 7 := by
  refine ⟨rfl, h3, ?_, ?_, ?_, ?_⟩
  · show y.parts.getD 0 0 + y.parts.getD 1 0 = 4
    omega
  · show y.parts.getD 0 0 + y.parts.getD 1 0 + 2 = 6
    omega
  · show y.parts.getD 0 0 + y.parts.getD 1 0 + 4 = 8
    omega
  · show y.parts.getD 0 0 + y.parts.getD 1 0 + 3 = 7
    omega

/-- slotOf undoes portNo on the eight slots. -/
theorem slotOf_portNo (y : Lay) (h3 : y.parts.getD 0 0 = 3) (h1 : y.parts.getD 1 0 = 1) {σ : ℕ}
    (hσ : σ < 8) : slotOf y (portNo y σ) = σ := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := firstM_ref y h3 h1
  interval_cases σ <;> simp [slotOf, portNo, f0, f1, f2, f3, f4, f5]

/-- At every place that libMZ keeps, in a column below 5,990, libM of backM y g A is A. -/
theorem lib_back (y : Lay) (h3 : y.parts.getD 0 0 = 3) (h1 : y.parts.getD 1 0 = 1)
    (A : ℕ → ℕ → ℕ → ℤ) {g s r c : ℕ} (C : CutM y g s r c) (hc : c < 5990) :
    libM y g (backM y g A) s r c = A s r c := by
  have hm : r % 65536 < 65536 := Nat.mod_lt _ (by norm_num)
  unfold libM
  rcases C with ⟨e, ⟨b, -, -⟩, h6⟩ | ⟨e, h7, -⟩
  · rw [if_pos e]
    unfold backM
    rw [slotOf_portNo y h3 h1 b, if_pos ⟨b, hm, hc⟩,
      if_neg (fun h => by have h0 := h6 h.1; omega), e, Nat.div_add_mod']
  · rw [if_neg (by omega), if_pos ⟨e, h7⟩]
    have s6 : slotOf y (firstM y 4) = 6 := slotOf_portNo y h3 h1 (σ := 6) (by norm_num)
    unfold backM
    rw [s6, if_pos ⟨by norm_num, hm, hc⟩, if_pos ⟨rfl, by omega⟩,
      show 2 * g - 2 = s by omega, show 7 * 65536 + r % 65536 = r by omega]

/-- The place at which the library reads a valid name lies in a column below 5,990. -/
theorem col_at (g : ℕ) (c : Cell) (hc : c.Valid DF) : (ownFF g c).place.2.2 < 5990 := by
  rcases Cm.Seg.ownFF_cases g c with e | ⟨-, hx, e⟩
  · rw [e]
    exact (Cm.Seg.plFF_in c hc).2
  · rw [e]
    obtain ⟨X, k, inst, j, i⟩ := c
    have hx' : X = .x0 := hx
    subst hx'
    exact (Cm.Seg.plFF_in ⟨.x8, k, inst, j, i⟩ hc).2

/-- A place of a segment with an even number below 24 lies in the library's shape. -/
theorem inShape_even {s r c : ℕ} (h2 : s % 2 = 0) (h24 : s < 24) (hr : r < 524288)
    (hc : c < 5990) : Cm.Seg.InShape (s, r, c) := by
  refine ⟨?_, ?_, ?_⟩
  · show s < 25
    omega
  · show r < 2 ^ (if s % 2 = 1 then 18 else 19)
    rw [if_neg (by omega)]
    norm_num
    exact hr
  · show c < (if s = 24 then Cm.Seg.colsHead else if s % 2 = 1 then Cm.Seg.colsAtt
      else Cm.Seg.colsFF)
    rw [if_neg (by omega), if_neg (by omega), Cm.Seg.colsFF_eq]
    exact hc

/-! ## The dictionary, backwards -/

section Back

variable {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF)
  (hp4 : h.p4 = true)

include hy S Z2 in
/-- A layout that the verifier returns at the reference sizes has three parts of af and one of
ad. -/
theorem parts_ref : y.parts.getD 0 0 = 3 ∧ y.parts.getD 1 0 = 1 := by
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  have L := laid2_of_layout hy
  refine ⟨?_, ?_⟩
  · rw [L.parts0, ← Z2.parts]
    rfl
  · rw [L.parts1, Z2.NAd]

include hy S Z Z2 hp4 in
/-- The library's reading of ANY family A of integer matrices as a trace of the feed-forward segment
of group g is, at every valid name, the cell that the verifier's rule reads in backM y g A. -/
theorem dict_back (g : ℕ) (A : ℕ → ℕ → ℕ → ℤ) (c : Cell) (hc : c.Valid DF) :
    Cm.Seg.TS.tM g A c = cellsOf DF (cellsAt y (backM y g A)) c := by
  obtain ⟨h3, h1⟩ := parts_ref hy S Z2
  rw [← dict_valid hy S Z Z2 hp4 g (backM y g A) c hc]
  exact (lib_back y h3 h1 A (cut_at hy S Z Z2 hp4 g c hc) (col_at g c hc)).symm

include hy S Z2 in
/-- If A is small at all places of the library's shapes, the matrices backM y g A are small. -/
theorem small_back {g : ℕ} (hg : g < 12) {A : ℕ → ℕ → ℕ → ℤ}
    (hb : ∀ q : Cb.Place, Cm.Seg.InShape q → |at' A q| < 2 ^ 18) : SmallM y (backM y g A) := by
  obtain ⟨h3, h1⟩ := parts_ref hy S Z2
  intro σ r c hz
  unfold backM
  rw [slotOf_portNo y h3 h1 hz.1]
  by_cases hin : σ < 8 ∧ r < 65536 ∧ c < 5990
  · rw [if_pos hin]
    obtain ⟨a1, a2, a3⟩ := hin
    by_cases h6 : σ = 6 ∧ 0 < g
    · rw [if_pos h6]
      exact hb (2 * g - 2, 7 * 65536 + r, c)
        (inShape_even (by omega) (by omega) (by omega) a3)
    · rw [if_neg h6]
      exact hb (2 * g, σ * 65536 + r, c) (inShape_even (by omega) (by omega) (by omega) a3)
  · rw [if_neg hin]
    norm_num

end Back

#print axioms slotOf_portNo
#print axioms lib_back
#print axioms dict_back
#print axioms small_back

end OnBytes.Road
