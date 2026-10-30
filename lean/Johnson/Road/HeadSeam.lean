-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSeam.lean: reader against owner: at every place that a segment of the library's
model may read, two sub-proofs' matrices give the dictionary D5 one value, if they agree at one
label.

The library's model has 25 segments. A segment reads its own cells and, at three kinds of places,
cells of an earlier segment (Cm.Seg.reads in Cm/SegLayout.lean): the feed-forward segment of a later
group reads the stream that left the group before; an attention segment reads four arrays of the
feed-forward segment of its group; the head reads the stream that left the last group. The verifier
has one sub-proof for each segment, and each sub-proof has matrices of its own: its own cells and
its copies of what it borrows. Johnson/Road/HeadDict.lean fills the library's family of matrices
from matrices that are named by the labels of the verifier's plans (D5). Here each sub-proof k has
its own matrices Z k. The theorem says: if reader and owner agree at the label of the borrowed
matrix, then at every place that segment k may read, D5 at Z k is D5 at the owner's matrices.

What is compared with what: the library's reads, its places and its two laws on the rows of the
slots qa and xout (Cm/SegLayoutProofs.lean) against D5, a definition of these files.

Main definitions: LabelsAgree (24 equations between matrices, each at one label).
Main theorems: labA_in (the label under which a later group's own list has the stream that comes
in); seam_reads.

The hypotheses. LabelsAgree: no theorem concludes it. It says that a sub-proof's copy of a matrix
has the entries of its owner's matrix: a matter of the commitments, not of layouts. With one family
Z for all sub-proofs it holds by definition (labelsAgree_one).

What is not claimed. The labels in the lists of attention's sub-proofs are not looked at: that the
copy of qa bears the owner's label there is not shown. For the later groups and the head it is
(labA_in with labA_tails of Johnson/Road/FormsKeysDictA.lean; labH_lent with labH_of_public of
Johnson/Road/HeadDict.lean). The equations are asked at all rows and columns; the places of cells
would serve. The program does not import this file.
-/
import Johnson.Road.HeadDict
import Cm.SegLayoutProofs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model.Layer (Lay matIx)
open Cm.Seg (at' reads plFF)

/-- The stream that comes into a later group has, in that group's own list, the label of the stream
that goes out of the group before. -/
theorem labA_in (y : Lay) {g : ℕ} (hg : 0 < g) :
    labA y g (matIx y).iXI = labA y (g - 1) (matIx y).iXO := by
  have e1 : labA y g (matIx y).iXI = g * 256 + (matIx y).iXO := if_pos ⟨rfl, by omega⟩
  have e2 : labA y (g - 1) (matIx y).iXO = (1 + (g - 1)) * 256 + (matIx y).iXO :=
    if_neg fun h => xo_ne_xi y h.1
  rw [e1, e2, show 1 + (g - 1) = g by omega]

/-- Reader and owner agree at the label of what is borrowed. Z k: the matrices of the sub-proof of
segment k, named by labels. ff: a later group's copy of the stream against the group before. att: an
attention sub-proof's copy of qa against its group. head: the head's copy of the stream against the
last group. -/
structure LabelsAgree (y : Lay) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) : Prop where
  ff : ∀ g, 0 < g → g < 12 → ∀ r c,
    Z (2 * g) (labA y (g - 1) (matIx y).iXO) r c =
      Z (2 * (g - 1)) (labA y (g - 1) (matIx y).iXO) r c
  att : ∀ g, g < 12 → ∀ r c,
    Z (2 * g + 1) (labA y g (matIx y).iQA) r c = Z (2 * g) (labA y g (matIx y).iQA) r c
  head : ∀ r c, Z 24 (labA y 11 (matIx y).iXO) r c = Z 22 (labA y 11 (matIx y).iXO) r c

/-- One family of matrices for all sub-proofs meets it. -/
theorem labelsAgree_one (y : Lay) (Z : ℕ → ℕ → ℕ → ℤ) : LabelsAgree y fun _ => Z :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

/-- **Reader against owner.** At every place q that segment k of the library's model may read, the
dictionary at the matrices of sub-proof k has the value that it has at the matrices of the sub-proof
of the segment q.1, which owns the place. hd: the library's shape of the head, any. At: letters for
attention's own segments. -/
theorem seam_reads (hd : Cm.Seg.Hd) (h : Model.Head.Shape) {y : Lay}
    (At : ℕ → ℕ → ℕ → ℕ → ℤ) {Z : ℕ → ℕ → ℕ → ℕ → ℤ} (A : LabelsAgree y Z) :
    ∀ k < Cm.Seg.nSeg, ∀ q ∈ reads hd k,
      at' (D5 h y (At k) (Z k)) q = at' (D5 h y (At q.1) (Z q.1)) q := by
  intro k _ q hq
  rcases hq with ⟨g, c, rfl, hg, hc, rfl⟩ | ⟨g, c, rfl, hg, hc, rfl⟩ | ⟨rfl,
    ⟨n, hn, hn24, rfl⟩ | ⟨φ, i, hφ, hi, rfl⟩⟩
  · have hv := Cm.Seg.ownFF_valid hd hg hc
    rw [Cm.Seg.nGr_eq] at hg
    rcases Cm.Seg.ownFF_cases g c with e | ⟨h0, _, e⟩
    · rw [e]
      rfl
    · rw [e] at hv ⊢
      show D5 h y (At (2 * g)) (Z (2 * g)) (2 * (g - 1)) (plFF { c with X := .x8 }).1
          (plFF { c with X := .x8 }).2 =
        D5 h y (At (2 * (g - 1))) (Z (2 * (g - 1))) (2 * (g - 1)) (plFF { c with X := .x8 }).1
          (plFF { c with X := .x8 }).2
      refine seam_D5 h y _ _ _ _ (g := g - 1) (t := 7) (by omega) (A.ff g h0 hg) ?_ _
      have hr := Cm.Seg.plFF_row _ hv.2.1
      rw [Cm.Seg.plFF_row_xout _ hv.2.1 rfl]
      rw [Cm.Seg.hSlot_eq] at hr ⊢
      omega
  · have hv := Cm.Seg.ownAtt_valid hd hg hc
    rw [Cm.Seg.nGr_eq] at hg
    rcases Cm.Seg.ownAtt_cases g c with e | ⟨c', e, hm⟩
    · rw [e]
      rfl
    · rw [e] at hv ⊢
      show D5 h y (At (2 * g + 1)) (Z (2 * g + 1)) (2 * g) (plFF c').1 (plFF c').2 =
        D5 h y (At (2 * g)) (Z (2 * g)) (2 * g) (plFF c').1 (plFF c').2
      refine seam_D5 h y _ _ _ _ (g := g) (t := 5) hg (A.att g hg) ?_ _
      have hr := Cm.Seg.plFF_row _ hv.2.1
      rw [Cm.Seg.plFF_row_qa _ hv.2.1 hm]
      rw [Cm.Seg.hSlot_eq] at hr ⊢
      omega
  · rw [hn24]
  · rw [place_x]
    rw [Cm.Seg.nFeat_x] at hφ
    rw [Cm.Seg.nT_eq] at hi
    have hrow : ((7 + φ / 64 / 5990) * 65536 + (φ % 64 * 2 ^ 10 + i)) / 65536 = 7 := by
      have e10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
      rw [e10]
      omega
    have key := seam_D5 h y (At 22) (At 24) (Z 22) (Z 24) (g := 11) (t := 7) (by omega) A.head hrow
      (φ / 64 % 5990)
    have e22 : 2 * 11 = 22 := by norm_num
    rw [e22] at key
    unfold Cm.Seg.at'
    dsimp only
    exact key

#print axioms labA_in
#print axioms labelsAgree_one
#print axioms seam_reads

end OnBytes.Road.Hd
