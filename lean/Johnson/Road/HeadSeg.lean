-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSeg.lean: the library's own segment of the output head, at matrices that are
stacked from the verifier's matrices.

The library states the conditions of the output head twice. On cells: the field relation of the
plain head (Cm.Plain.TP.RF, Cm/TargetPHead.lean): every key is an entry of its table, every identity
is 0, every cell is small. On matrices: segment 24 of its partition (Cm.Seg.TS.segHead,
Cm/TargetSegHead.lean), whose forms read the matrices at the places of the library's layout
(Cm/SegLayout.lean). Johnson/Road/HeadPlace.lean reads cells in the verifier's matrices by the
verifier's rule (cellsH) and stacks the verifier's matrices into a family of the library's shape
(stackedH). This file joins the two: the conditions on the cells cellsH are the conditions of the
library's segment at the matrices stackedH.

What is compared with what. On one side the library's relation at cells that are read in the
verifier's matrices by the verifier's numbers; on the other the library's segment at the stacked
matrices. What carries it: readsAt_cellsH and tH_cellsH (Johnson/Road/HeadPlace.lean), which set the
verifier's numbers against the library's places; the library's head_holds, head_holds_int, key_same
and idn_same (Cm/TargetSegHeadAsm.lean, Cm/SegHeadAsm.lean).

Main theorems.
 - same_cellsH, seg_iff_cells: for matrices with entries in the challenge field: the segment holds
   at the stacked matrices if and only if keys and identities at cellsH are as asked.
 - matHolds_iff_cells, matHolds_of_rf, rf_of_matHolds; seg_of_rf; castM_stackedH, seg_of_rf_cast,
   seg_of_rf_index: for integer matrices: from the field relation over the challenge field at
   cellsH to the segment at the stacked matrices, and back.
 - planH2_label, owner_ix, matsH_last, lent_label: the public half of the hypothesis LentH: the last
   matrix of the head's list is marked as another sub-proof's, and it bears the label that the
   matrix of the stream that leaves the last group of layers has in that group's own list.

The hypotheses, and where they are met: those of readsAt_cellsH (Johnson/Road/HeadPlace.lean).
LentH, that the head's copy of the stream has the lender's entries, is concluded by no theorem.

What stackedH holds outside the verifier's shapes. A matrix of the verifier's list is here a
function on all rows and columns, and stackedH hands it on as it is. So in segment 24 the rows of hd
from 16,384 on and its columns from 640 on (its sizes by numH_of_layout), and the slots 6 and 7,
under which the list has bH and the borrowed stream, hold whatever the function holds there, not 0
as the matrices that the library makes from a trace. The theorems here do not read these places: the
segment's conditions reach the matrices through the names of the record Same alone (same_cellsH, the
library's key_same and idn_same). A statement on the whole of a committed matrix would have to speak
of them.

What is not claimed. Nothing here derives the relation, or the segment's conditions, from a
verifier's acceptance. Nothing is said of the other 24 segments. The program does not import this
file.
-/
import Johnson.Road.HeadReads
import Johnson.Road.HeadDown
import Johnson.Road.HeadReq
import Cm.RelTrue

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat)
open Inst.Model.Head (nT nD nV nFeat InLut)
open Inst.Model.All (DF)
open OnBytes.Model (TMat HTailF2 Settings)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL Border Owner HPlanH2 matsH planH2)
open OnBytes.Model.Verify (borderOf ownerOf)

section Seg

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-! ## Matrices with entries in the challenge field -/

/-- The library's reading of the stacked matrices and the cells that are read in the verifier's
matrices agree at the names that the plain head reads. -/
theorem same_cellsH (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats Cb.Gl.E) (Ma : ℕ → ℕ → ℕ → Cb.Gl.E) (Mh : Mats Cb.Gl.E)
    (hlent : LentH h y Mh (Mg 11)) :
    Cm.Seg.Same (Cm.Seg.TS.tH (stackedH y Mg Ma Mh)) (cellsH h L (borderOf y) Mh) :=
  ⟨fun φ _ _ hi => (tH_cellsH hF hL hl S Z Z2 Mg Ma Mh hlent hi).1 φ,
    fun φ hφ _ hi => (tH_cellsH hF hL hl S Z Z2 Mg Ma Mh hlent hi).2.1 φ hφ,
    fun φ hφ _ hi => (tH_cellsH hF hL hl S Z Z2 Mg Ma Mh hlent hi).2.2.1 φ
      (Nat.lt_of_lt_of_le hφ (by decide)),
    fun φ hφ _ hi => (tH_cellsH hF hL hl S Z Z2 Mg Ma Mh hlent hi).2.2.2 φ hφ⟩

/-- **The library's segment of the head at the stacked matrices** holds if and only if, at the cells
that are read in the verifier's matrices, every key of the plain head is an entry of its table and
each of the 17 identities is 0. W: any index matrix; the output matrix is what the library's layout
reads in it. -/
theorem seg_iff_cells (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats Cb.Gl.E) (Ma : ℕ → ℕ → ℕ → Cb.Gl.E) (Mh : Mats Cb.Gl.E)
    (hlent : LentH h y Mh (Mg 11)) (np : NormPar) (x : Instance ppref) (W : ℕ → ℕ → Cb.Gl.F) :
    (Cm.Seg.TS.segHead np).Holds Cm.Seg.TS.fmtRef x W (stackedH y Mg Ma Mh) ↔
      (∀ f a i, a < Cm.Plain.len f → i < nT → InLut (Cm.Plain.TP.tableOf f)
        (Cm.Plain.TP.key np (cellsH h L (borderOf y) Mh) (Cm.Seg.TS.HW W) (Cm.reqOf x) f a i)) ∧
      ∀ i < nT, ∀ k < 17, Cm.Plain.idn np (cellsH h L (borderOf y) Mh) i k = 0 := by
  have hS := same_cellsH hF hL hl S Z Z2 Mg Ma Mh hlent
  rw [Cm.Seg.TS.head_holds np x W _]
  constructor
  · rintro ⟨hK, hI⟩
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_⟩
    · rw [← Cm.Seg.TS.key_same hS np _ _ f ha hi]
      exact (Down.inLut_gl _ _).2 (hK f a i ha hi)
    · rw [← Cm.Seg.idn_same hS np hi hk]
      exact hI i hi k hk
  · rintro ⟨hK, hI⟩
    refine ⟨fun f a i ha hi => ?_, fun i hi k hk => ?_⟩
    · rw [Cm.Seg.TS.key_same hS np _ _ f ha hi]
      exact (Down.inLut_gl _ _).1 (hK f a i ha hi)
    · rw [Cm.Seg.idn_same hS np hi hk]
      exact hI i hi k hk

/-! ## Integer matrices -/

/-- For integer matrices: keys and identities in the challenge field at the library's places of the
stacked matrices are as asked if and only if, modulo p, they are so at the cells that are read in
the verifier's matrices. -/
theorem matHolds_iff_cells (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11))
    (np : NormPar) (x : Instance ppref) (Wz : Mat) :
    Down.MatHolds np x Wz (stackedH y Mg Ma Mh) ↔
      (∀ f a i, a < Cm.Plain.len f → i < nT → InLut (Cm.Plain.TP.tableOf f)
        (Cm.Plain.TP.key np ((cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
          (Cm.TP.castH Cb.Gl.p Wz) (Cm.reqOf x) f a i)) ∧
      ∀ i < nT, ∀ k < 17, Cm.Plain.idn np ((cellsH h L (borderOf y) Mh).cast Cb.Gl.F) i k = 0 :=
  Down.down np x Wz _ _ (readsAt_cellsH hF hL hl S Z Z2 Mg Ma Mh hlent)

/-- **From the field relation at the verifier's cells to the library's matrices.** If the field
relation of the plain head holds over the challenge field at the cells that are read in integer
matrices of the verifier's list, with an output matrix Hz that agrees on its 5,120 x 202,048 entries
with the one that the library's layout reads in the index matrix Wz, then keys and identities at the
library's places of the stacked matrices are as the head's segment asks. -/
theorem matHolds_of_rf (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11))
    {np : NormPar} {x : Instance ppref} {Wz Hz : Mat}
    (hHz : ∀ j < nD, ∀ v < nV,
      Hz j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    (rf : Cm.Plain.TP.RF (F := Cb.Gl.E) np (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
      (cellsH h L (borderOf y) Mh)) :
    Down.MatHolds np x Wz (stackedH y Mg Ma Mh) := by
  have r1 := Down.plainRF_gl.1 rf
  have r2 : Cm.Plain.TP.RF (F := ZMod Cb.Gl.p) np (Cm.TP.castH Cb.Gl.p Wz) (Cm.reqOf x)
      (cellsH h L (borderOf y) Mh) :=
    HeadReq.plainRF_of_mat (fun j hj v hv => by rw [hHz j hj v hv]) (fun i _ _ => x.w_lt i) r1
  exact (matHolds_iff_cells hF hL hl S Z Z2 Mg Ma Mh hlent np x Wz).2 ⟨r2.keys, r2.idns⟩

/-- And back, with the bound on the cells. -/
theorem rf_of_matHolds (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11))
    {np : NormPar} {x : Instance ppref} {Wz : Mat}
    (small : Cm.Plain.Small (2 ^ 18) (cellsH h L (borderOf y) Mh))
    (hM : Down.MatHolds np x Wz (stackedH y Mg Ma Mh)) :
    Cm.Plain.TP.RF (F := Cb.Gl.E) np (fun j v =>
      (((Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v : ℤ) : Cb.Gl.E))
      (Cm.reqOf x) (cellsH h L (borderOf y) Mh) :=
  Down.plainRF_gl.2 (Down.rf_of_mat (readsAt_cellsH hF hL hl S Z Z2 Mg Ma Mh hlent) small hM)

/-- **The library's own segment 24 at matrices stacked from the verifier's.** Under the hypotheses
of matHolds_of_rf the head's segment of the library's partition holds, for the request x and the
index matrix Wz, at the stacked matrices read in the challenge field. -/
theorem seg_of_rf (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11))
    {np : NormPar} {x : Instance ppref} {Wz Hz : Mat}
    (hHz : ∀ j < nD, ∀ v < nV,
      Hz j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    (rf : Cm.Plain.TP.RF (F := Cb.Gl.E) np (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
      (cellsH h L (borderOf y) Mh)) :
    (Cm.Seg.TS.segHead np).Holds Cm.Seg.TS.fmtRef x (fun r c => ((Wz r c : ℤ) : Cb.Gl.F))
      (Cb.Partition.castM (E := Cb.Gl.E) (stackedH y Mg Ma Mh)) :=
  (Down.matHolds_iff_seg np x Wz _).1 (matHolds_of_rf hF hL hl S Z Z2 Mg Ma Mh hlent hHz rf)

/-- Reading the stacked integer matrices in the challenge field is stacking the matrices that are
read in the challenge field. -/
theorem castM_stackedH (y : Lay) (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) :
    Cb.Partition.castM (E := Cb.Gl.E) (stackedH y Mg Ma Mh) =
      stackedH y (fun g a r c => ((Mg g a r c : ℤ) : Cb.Gl.E))
        (fun g r c => ((Ma g r c : ℤ) : Cb.Gl.E)) (fun a r c => ((Mh a r c : ℤ) : Cb.Gl.E)) := by
  funext s r c
  exact (stackedH_map (fun z : ℤ => (z : Cb.Gl.E)) y Mg Ma Mh s r c).symm

/-- The same with the casts inside: the matrices of the verifier's lists, read in the challenge
field as a world of its check holds them, and then stacked. -/
theorem seg_of_rf_cast (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11))
    {np : NormPar} {x : Instance ppref} {Wz Hz : Mat}
    (hHz : ∀ j < nD, ∀ v < nV,
      Hz j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    (rf : Cm.Plain.TP.RF (F := Cb.Gl.E) np (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
      (cellsH h L (borderOf y) Mh)) :
    (Cm.Seg.TS.segHead np).Holds Cm.Seg.TS.fmtRef x (fun r c => ((Wz r c : ℤ) : Cb.Gl.F))
      (stackedH y (fun g a r c => ((Mg g a r c : ℤ) : Cb.Gl.E))
        (fun g r c => ((Ma g r c : ℤ) : Cb.Gl.E)) (fun a r c => ((Mh a r c : ℤ) : Cb.Gl.E))) := by
  rw [← castM_stackedH]
  exact seg_of_rf hF hL hl S Z Z2 Mg Ma Mh hlent hHz rf

/-- The same for an index of the library's relation: weight tensors j, with the digit matrix that
the library makes of them (Cm.Idx.ofIndex, Cm/RelTrue.lean) as the index matrix. -/
theorem seg_of_rf_index (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) (hlent : LentH h y Mh (Mg 11))
    {np : NormPar} {x : Instance ppref} (j : Inst.Model.Index ppref)
    (rf : Cm.Plain.TP.RF (F := Cb.Gl.E) np (fun a v => ((j.val.H a v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
      (cellsH h L (borderOf y) Mh)) :
    (Cm.Seg.TS.segHead np).Holds Cm.Seg.TS.fmtRef x
      (fun r c => (((Cm.Idx.ofIndex j).mat r c : ℤ) : Cb.Gl.F))
      (Cb.Partition.castM (E := Cb.Gl.E) (stackedH y Mg Ma Mh)) :=
  seg_of_rf hF hL hl S Z Z2 Mg Ma Mh hlent (Wz := (Cm.Idx.ofIndex j).mat) (Hz := j.val.H)
    (fun a _ v _ =>
      congrArg (fun w : Inst.Model.Weights => w.H a v) (Cm.weights_ofIndex j).symm) rf

end Seg

/-! ## The public half of LentH: whose matrix the head borrows -/

/-- The plan that planH2 returns, with the origin of the stream's label: the list of the smallness
test is matsH with the label of the matrix that stands under the number O.iXO in the owner's list.
-/
theorem planH2_label {g : Settings} {h : Model.Head.Shape} {L : HL} {b : Border} {O : Owner}
    {NGr lkW : ℕ} {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    ∃ stream, O.tl.mats[O.iXO]? = some stream ∧
      hp.tl.mats = matsH h L b (1 + NGr) stream.aId := by
  unfold Model.Head.planH2 at hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨pc, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hs : O.tl.mats[O.iXO]? with
  | none =>
    simp only [hs] at hpl
    have h' : (Except.error "internal-h-owner-TX" : Except String HPlanH2) = .ok hp := hpl
    cases h'
  | some M0 =>
    simp only [hs] at hpl
    obtain ⟨stream, hst, hpl⟩ := ok_of_bind (x := (pure M0 : Except String TMat)) hpl
    have e0 : M0 = stream := Except.ok.inj hst
    obtain ⟨t1, h1, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨r, hr, hpl⟩ := ok_of_bind hpl
    obtain ⟨t2, Fp, Tp⟩ := r
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨Tp2, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨t3, h3, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    have e := (Except.ok.inj hpl).symm
    subst e
    exact ⟨stream, by rw [e0], (ownerHeld_keeps h3).1.trans
      ((addTrees_keeps hr).1.trans (shape_mats h1).1)⟩

/-- What the verifier's public part hands the head's plan of the layers: the record of the smallness
test of the plan of the last group, and, as the number of the stream that leaves the group, the
number that the layers' own list has for it. -/
theorem owner_ix {y : Lay} {G : Array Model.Layer.HPlan2} {O : Owner}
    (hO : ownerOf y G = .ok O) : ∃ P, G.back? = some P ∧ O.tl = P.tl ∧ O.iXO = firstM y 5 := by
  unfold Model.Verify.ownerOf at hO
  cases hb : G.back? with
  | none =>
    simp only [hb] at hO
    have h' : (Except.error "internal-h-owner-TX" : Except String Owner) = .ok O := hO
    cases h'
  | some P =>
    simp only [hb] at hO
    have e := (Except.ok.inj hO).symm
    subst e
    exact ⟨P, rfl, rfl, rfl⟩

/-- The last matrix of the list matsH, for hf in four parts: it is marked as a matrix of another
sub-proof, the first of those that the head reads, and bears the label sid. -/
theorem matsH_last {h : Model.Head.Shape} (L : HL) (b : Border) (gid sid : ℕ) (hN : h.NHf = 4) :
    ((matsH h L b gid sid).getD (h.NHf + 3) {}).aId = sid ∧
    ((matsH h L b gid sid).getD (h.NHf + 3) {}).kind = 1 ∧
    ((matsH h L b gid sid).getD (h.NHf + 3) {}).foreign = some 0 := by
  unfold Model.Head.matsH
  rw [hN]
  exact ⟨rfl, rfl, rfl⟩

/-- **Whose matrix the head borrows.** If the owner's record is what the verifier's public part
makes of the plans G of the groups of layers, and the head's plan is what planH2 returns on it, then
the matrix with the number NHf + 3 of the head's list, in which cellsH reads the stream, is marked
as a matrix of another sub-proof and bears the label of the matrix with the number firstM y 5 in the
list of the last group's plan: the number under which stackedH reads the stream in the lender's
list. That two matrices with one label have the same entries is not a public fact: it is the
hypothesis LentH. -/
theorem lent_label {y : Lay} {G : Array Model.Layer.HPlan2} {O : Owner}
    (hO : ownerOf y G = .ok O) {g : Settings} {h : Model.Head.Shape} {L : HL} {b : Border}
    {NGr lkW : ℕ} {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) (hN : h.NHf = 4) :
    ∃ P stream, G.back? = some P ∧ P.tl.mats[firstM y 5]? = some stream ∧
      (hp.tl.mats.getD (h.NHf + 3) {}).aId = stream.aId ∧
      (hp.tl.mats.getD (h.NHf + 3) {}).kind = 1 ∧
      (hp.tl.mats.getD (h.NHf + 3) {}).foreign = some 0 := by
  obtain ⟨P, hP, e1, e2⟩ := owner_ix hO
  obtain ⟨stream, hs, hm⟩ := planH2_label hpl
  rw [e1, e2] at hs
  obtain ⟨a1, a2, a3⟩ := matsH_last L b (1 + NGr) stream.aId hN
  rw [← hm] at a1 a2 a3
  exact ⟨P, stream, hP, hs, a1, a2, a3⟩

#print axioms same_cellsH
#print axioms seg_iff_cells
#print axioms matHolds_iff_cells
#print axioms matHolds_of_rf
#print axioms rf_of_matHolds
#print axioms seg_of_rf
#print axioms seg_of_rf_cast
#print axioms seg_of_rf_index
#print axioms planH2_label
#print axioms owner_ix
#print axioms lent_label

end OnBytes.Road.Hd
