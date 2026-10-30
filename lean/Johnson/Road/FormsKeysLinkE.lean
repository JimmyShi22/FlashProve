-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLinkE.lean: the conditions of an even segment of the library's model at the
library's matrices cut to the shapes of the verifier's list.

Johnson/Road/FormsKeysIdn.lean says the conditions of segment 2 g of the library's model on the
cells of integer matrices Mz that are numbered as the verifier's list for a group numbers its
matrices (the cells named by the library's numbers of features, at the part, row and column that
the verifier's rule gives a feature), for any integer matrices of the library's that hold those
cells at the library's places. Johnson/Road/FormsKeysDictZ.lean makes such matrices, libMZ y g Mz,
that are 0 outside the rows and columns of the list's shapes. This file joins the two, in the
letters in which the library's theorem on all 25 segments (model_force in Cm/TargetSegModel.lean)
asks a segment's conditions: before gluing, at the format fmtRef, at the cast cM.

What is compared with what. As in Johnson/Road/FormsKeysIdn.lean.

Main theorems: cM_eq (the library's two names for the cast of integer matrices are one); holds_cM
(any matrices that hold the cells); holds_mz_file (at libMZ); link_mz_file (the two halves apart);
link_even (with the bound on the entries: small Mz, identities and key vectors give small matrices
of the library's at which the segment's conditions hold).

Who reads the target. Holds of Cm.Seg.TS.segM s k at fmtRef and cM M, for all k below 25, with a
bound on the cells, is the hypothesis of the library's model_force. Twelve of the 25 are said here,
one group at a time, each at matrices of its own.

At which sizes. DF, the library's Dim.ref, alone; fmtRef; the reference tables; groups of four
layers, the first layer 4 g; the fields Cb.Gl.F and Cb.Gl.E; casts of integers.

The hypotheses, and that they can be met. As in Johnson/Road/FormsKeysIdn.lean; hD is met by
dict_mz.

What is not claimed. All that Johnson/Road/FormsKeysIdn.lean does not claim. That Mz is small: it
is the hypothesis SmallM of link_even (Johnson/Road/FormsKeysDictZ.lean); no converse is stated for
it. That the matrices of neighbouring groups agree where a row is handed on. The program does
not import this file.
-/
import Johnson.Road.FormsKeysIdn
import Johnson.Road.FormsKeysDictZ

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model.Layer (Lay Shape Scales layout)
open Inst.Model (Scl Tables Mat ppref)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Cell Idn idnVal embR keyVec layerR lut aC)

/-- The library has two names for integer matrices carried into its larger field. -/
theorem cM_eq (M : ℕ → ℕ → ℕ → ℤ) :
    Cm.Seg.TS.cM M = Cb.Partition.castM (E := Cb.Gl.E) M := rfl

/-- holds_end (Johnson/Road/FormsKeysIdn.lean) with the library's cM: the whole conditions of
segment 2 g of the library's model, before gluing, at integer matrices M that hold the cells of Mz.
-/
theorem holds_cM (y : Lay) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (M : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c) (h : Shape)
    (sc : Scales) (s : Cm.Scales)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = s.kap (4 * g + l)) (x : Cm.Seg.XI) :
    (Cm.Seg.TS.segM s (2 * g)).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi)
        (Cm.Seg.TS.cM M) ↔
    (∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0) ∧
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) :=
  holds_end y Mz Wi hg M hD h sc s hw x

section Port

variable {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
  (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF) (hp4 : h.p4 = true)

include hy S Z Z2 hp4

/-- One group, at the library's matrices libMZ y g Mz (Johnson/Road/FormsKeysDictZ.lean): made from
integer matrices Mz in the numbering of the verifier's list, and 0 outside the rows and columns of
the list's shapes; under the library's table of scales made from the verifier's scale file, with
any final normalisation. -/
theorem holds_mz_file (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (sc : Scales)
    (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) :
    (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).Holds Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cm.Seg.TS.cM (libMZ y g Mz)) ↔
    (∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0) ∧
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) :=
  holds_cM y Mz Wi hg (libMZ y g Mz) (fun c hc => dict_mz hy S Z Z2 hp4 g Mz c hc) h sc _
    (words_file h sc nf hg) x

/-- The two halves apart, in the letters in which a link's identities and keys are asked: every
family of identities of the segment is 0 at every vertex; the keys' half. -/
theorem link_mz_file (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (sc : Scales)
    (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) :
    ((∀ f ∈ (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).idn, ∀ b < 2 ^ f.v,
        f.val Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi) (Cm.Seg.TS.cM (libMZ y g Mz)) b = 0) ↔
      (∀ j : Idn, j.Valid DF (decide (g = 0)) →
        idnVal (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0)) ∧
    (KeysHold (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)) Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cm.Seg.TS.cM (libMZ y g Mz)) ↔
      (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
        ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
            Cb.Tab Cb.Gl.F).set,
          keyVec (scl := sclOf h sc g 4) DF
              (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
              Inst.Model.tbRef (4 * g)
              (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
            algebraMap Cb.Gl.F Cb.Gl.E u)) :=
  ⟨(idn_end y Mz Wi hg (libMZ y g Mz) (fun c hc => dict_mz hy S Z Z2 hp4 g Mz c hc) h sc _
      (words_file h sc nf hg) x).symm,
    (keys_end y Mz Wi hg (libMZ y g Mz) (fun c hc => dict_mz hy S Z Z2 hp4 g Mz c hc) h sc _
      (words_file h sc nf hg) x).symm⟩

/-- One group in order. If the entries of Mz inside the shapes of the verifier's list are below
2^18 in size, all identities of the group vanish on the cells of Mz, and all entries of the eight
key vectors on them are images of entries of the library's reference tables, then every entry of
libMZ y g Mz is below 2^18 in size and the conditions of segment 2 g of the library's model hold at
it. -/
theorem link_even (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (sc : Scales)
    (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) (H : SmallM y Mz)
    (hI : ∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0)
    (hV : ∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) :
    (∀ s r c, |libMZ y g Mz s r c| < 2 ^ 18) ∧
      (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).Holds Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cm.Seg.TS.cM (libMZ y g Mz)) :=
  ⟨small_all H g, (holds_mz_file hy S Z Z2 hp4 Mz Wi hg sc nf x).mpr ⟨hI, hV⟩⟩

end Port

#print axioms cM_eq
#print axioms holds_cM
#print axioms holds_mz_file
#print axioms link_mz_file
#print axioms link_even

end OnBytes.Road
