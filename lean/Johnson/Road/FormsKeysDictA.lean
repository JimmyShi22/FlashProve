-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysDictA.lean: the dictionary of cells of all feed-forward segments, with the
verifier's matrices named by the labels of its plan.

Johnson/Road/FormsKeysDict.lean fills the library's matrices of all groups of layers from matrices
Mz g n, named by the group and the number in the group's list, and asks that the matrix that comes
into a group holds what went out of the group before (Seam). The verifier's plan does not name a
matrix so. Its list for a group (tailsOf in OnBytes/Model/LayerPlan.lean) gives each entry a label:
256 (1 + g) + the number; and, from the second group on, it gives the entry of the stream that comes
in the label of the stream that goes out of the group before. This file names the matrices by these
labels. Then the two are one letter, and nothing is asked.

What is compared with what. labA_tails: a formula of this file for the label against the verifier's
own tailsOf. dict_lab: the library's reading tM (Cm/TargetSegFFAffPass.lean) of matrices of this
file against cellsOf and cellsAt of these files.

Main definitions, all of this file: labA, mzA, libOfA.
Main theorems.
 - labA_tails: labA y g n is the label of entry n of the verifier's list for group g.
 - seam_mzA: matrices that are named by labels meet Seam.
 - dict_lab: for g < 12, tM g (libOfA y Ma) is, at every valid name, the cell that the verifier's
   rule reads in the matrices with the labels of group g.

The hypotheses. dict_lab: those of dict_valid (FormsKeysDict.lean, whose head says where they are
met: at the full-size example alone). labA_tails: the group is one of the layout's groups, and the
number is below the length of the list.

Which value is which: the labels are public numbers; the entries of the matrices are hidden values,
here any integers.

What is not claimed. That a matrix with a label of an earlier group is the matrix to which that
group's sub-proof committed: the plan marks the entry so (kind 1, a matrix of an earlier sub-proof),
and how the smallness test ties it to the owner's commitment is not looked at. What the head of
FormsKeysDict.lean does not claim is not claimed here either: the entries' size; which number of the
list is which matrix. libOfA is 0 in the segments of attention and of the head. The program does not
import this file.
-/
import Johnson.Road.FormsKeysDict
import OnBytes.Model.LayerPlan

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Lay layout tailsOf matIx)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Cell)
open Cm.Seg (at' ownFF)

/-! ## The labels -/

/-- The label of entry n of the list of matrices of group g: 256 (1 + g) + n; but for the stream
that comes into a later group the label of the stream that goes out of the group before. -/
def labA (y : Lay) (g n : ℕ) : ℕ :=
  if n = (matIx y).iXI ∧ g ≠ 0 then g * 256 + (matIx y).iXO else (1 + g) * 256 + n

/-- Member i of the array of the values of fn at 0 to n - 1. -/
theorem range_map_at {α : Type} (n : ℕ) (fn : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    ((Array.range n).map fn).getD i d = fn i := by
  simp [Array.getD, hi]

/-- Member n of the array of the values of F at the members of a list with their numbers. -/
theorem zipIdx_map_at {α β : Type} (l : List α) (F : α × ℕ → β) (d : β) {n : ℕ}
    (hn : n < l.length) : (l.zipIdx.map F).toArray.getD n d = F (l[n], n) := by
  simp [Array.getD, hn]

/-- labA is the label that the verifier's plan gives. -/
theorem labA_tails (y : Lay) {g n : ℕ} (hg : g < y.NGr)
    (hn : n < y.parts.getD 0 0 + y.parts.getD 1 0 + 5) :
    (((tailsOf y).getD g {}).mats.getD n {}).aId = labA y g n := by
  have hb : ((n == (matIx y).iXI && g != 0) = true) ↔ (n = (matIx y).iXI ∧ g ≠ 0) := by simp
  unfold tailsOf labA
  dsimp only
  rw [range_map_at _ _ _ hg]
  dsimp only
  rw [zipIdx_map_at _ _ _ (by
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega)]
  dsimp only
  by_cases h1 : n = (matIx y).iXI ∧ g ≠ 0
  · rw [if_pos h1, if_pos (hb.mpr h1)]
  · rw [if_neg h1, if_neg fun h => h1 (hb.mp h)]

/-! ## Matrices that are named by labels -/

/-- The matrices of group g, from matrices Ma that are named by labels. -/
def mzA (y : Lay) (Ma : ℕ → ℕ → ℕ → ℤ) (g : ℕ) : Mats ℤ := fun n r c => Ma (labA y g n) r c

/-- The two streams have different numbers in the list. -/
theorem xo_ne_xi (y : Lay) : (matIx y).iXO ≠ (matIx y).iXI := by
  show y.parts.getD 0 0 + y.parts.getD 1 0 + 3 ≠ y.parts.getD 0 0 + y.parts.getD 1 0 + 4
  omega

/-- Matrices that are named by labels meet Seam: the stream that comes into a later group and the
stream that goes out of the group before have one label. -/
theorem seam_mzA (y : Lay) (Ma : ℕ → ℕ → ℕ → ℤ) {g : ℕ} (hg : 0 < g) : Seam y (mzA y Ma) g := by
  intro r c
  show Ma (labA y g (matIx y).iXI) r c = Ma (labA y (g - 1) (matIx y).iXO) r c
  have e1 : labA y g (matIx y).iXI = g * 256 + (matIx y).iXO := if_pos ⟨rfl, by omega⟩
  have e2 : labA y (g - 1) (matIx y).iXO = (1 + (g - 1)) * 256 + (matIx y).iXO :=
    if_neg fun h => xo_ne_xi y h.1
  rw [e1, e2, show 1 + (g - 1) = g by omega]

/-- The library's matrices for the twelve groups, filled from matrices that are named by labels. 0
in the segments with an odd number and from segment 24 on. -/
def libOfA (y : Lay) (Ma : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if s % 2 = 0 ∧ s < 24 then Ma (labA y (s / 2) (portNo y (r / 65536))) (r % 65536) c else 0

/-- Below segment 24 it is libOf at the matrices mzA. -/
theorem libOfA_eq (y : Lay) (Ma : ℕ → ℕ → ℕ → ℤ) {s : ℕ} (hs : s < 24) (r c : ℕ) :
    libOfA y Ma s r c = libOf y (mzA y Ma) s r c := by
  unfold libOfA libOf
  by_cases h2 : s % 2 = 0
  · rw [if_pos ⟨h2, hs⟩, if_pos h2]
    rfl
  · rw [if_neg fun h => h2 h.1, if_neg h2]

/-! ## The dictionary -/

/-- For all twelve groups in one family of matrices, with nothing asked on the seam. The library's
reading of libOfA y Ma as a trace of the segment of group g is, at every valid name, the cell that
the verifier's rule reads in the matrices with the labels of group g. -/
theorem dict_lab {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF)
    (hp4 : h.p4 = true) (Ma : ℕ → ℕ → ℕ → ℤ) {g : ℕ} (hg : g < 12) (c : Cell)
    (hc : c.Valid DF) :
    Cm.Seg.TS.tM g (libOfA y Ma) c = cellsOf DF (cellsAt y (mzA y Ma g)) c := by
  rw [← dict_all hy S Z Z2 hp4 (mzA y Ma) g (fun h0 => seam_mzA y Ma h0) c hc]
  show at' (libOfA y Ma) (ownFF g c).place = at' (libOf y (mzA y Ma)) (ownFF g c).place
  rcases Cm.Seg.ownFF_cases g c with e | ⟨h0, _, e⟩
  · rw [e]
    exact libOfA_eq y Ma (s := 2 * g) (by omega) _ _
  · rw [e]
    exact libOfA_eq y Ma (s := 2 * (g - 1)) (by omega) _ _

#print axioms labA_tails
#print axioms seam_mzA
#print axioms dict_lab

end OnBytes.Road
