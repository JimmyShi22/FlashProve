-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLinkL.lean: an even link is in order, from statements on integer matrices in
the numbering of the verifier's lists.

Johnson/Road/Lane5.lean states a premise on integer matrices, link by link, from which the
library's theorems reach its relation: link k is in order (LinkOK) if its own cells are small and
the conditions of segment k of the library's model hold at its matrices. This file gives that
record for the twelve even links, the feed-forward segments, from three statements (LayerOrd) on
the integer matrices behind a group's sub-proof, numbered as the verifier's list numbers them; and
reads the record back.

What is compared with what. As in Johnson/Road/FormsKeysIdn.lean: the library's identities and key
vectors on cells that these files' dictionary (cellsOf, cellsAt) names in integer matrices Mz,
against the conditions of the library's segment at matrices made from Mz. The cells are named by
the library's numbers of features, at the part, row and column that the verifier's rule gives a
feature. No function of the verifier's sub-proof stands in a statement.

What LayerOrd speaks of beside Mz: one integer matrix Wi of weights, read by the library's layout
(layerR, embR at ppref and kRef), which is a matrix of no link's sub-proof; the request x (its
tokens, in the first group); the scale file; the library's reference tables (lut tbRef), not the
verifier's.

Main definitions: LayerOrd. Main theorems: linkOK_even, linkOK_layer; linkOK_even_says;
layerOrd_iff.

layerOrd_iff is an equivalence: with the bound, LayerOrd and LinkOK say the same. The clauses of
the library's segment are restated along a renumbering of places, from the library's (segment, row,
column) to (number in the list, row, column); they are not derived from anything. What is won is
the dictionary, and no step toward a proof file.

Who reads the target. LinkOK at all 25 links, with the seams, is the premise of
Johnson/Road/Lane5.lean. Twelve of the 25 are given here, each at matrices of its own; the seams
are not.

At which sizes. DF, the library's Dim.ref, alone; all else as in Johnson/Road/FormsKeysLinkE.lean.

The hypotheses, and that they can be met. hy, S, Z, Z2, hp4, g < 12: see
Johnson/Road/FormsKeysTieP.lean. H, hI, hV are the three clauses of LayerOrd. They are met together
at one made-up value (Johnson/Road/FormsKeysLinkW.lean); that they hold of the matrices behind any
proof file is not shown here.

What is not claimed. All that Johnson/Road/FormsKeysIdn.lean and Johnson/Road/FormsKeysLinkE.lean
do not claim. That the verifier reads its weights by the library's layout, or that its tables are
the library's. Which array, tensor and call stands where is the library's, by the definition of
LayerOrd: that the verifier's tensors lie where cellsOf reads is tied_cellsOf
(Johnson/Road/FormsKeysFits.lean), which no term joins with this file. The program does not import
this file.
-/
import Johnson.Road.FormsKeysLinkE
import Johnson.Road.Lane5

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

/-- A group of layers is in order at integer matrices Mz, an integer matrix Wi of weights and a
request x. Mz: the integer matrices behind the group's sub-proof, numbered as the verifier's list
numbers them. small: the entries of Mz inside the shapes of the list are below 2^18 in size. idn:
all identities of the group vanish on the cells of Mz. key: all entries of the group's eight key
vectors on these cells, below the vectors' lengths, are images of entries of the library's
reference tables. The cells of Mz are the cells named by the library's numbers of features, at the
part, row and column that the verifier's rule gives a feature. Identities and keys are equations in
the field Cb.Gl.E, on the casts of Mz and Wi. Beside Mz the clauses speak of Wi, read by the
library's layout (layerR, embR at ppref and kRef), which is a matrix of no link's sub-proof; of the
request x (its tokens, in the first group); of the scale file sc at the shape h, from which the
table of scales is made; and of the library's tables (lut tbRef), not the verifier's. y: the
layout; g: the number of the group. -/
structure LayerOrd (h : Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat)
    (x : Cm.Seg.XI) : Prop where
  small : SmallM y Mz
  idn : ∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0
  key : ∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u

variable {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
  (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF) (hp4 : h.p4 = true)

include hy S Z Z2 hp4

/-- Link 2 g is in order (LinkOK in Johnson/Road/Lane5.lean) at the library's matrices libMZ y g
Mz, under the three clauses of LayerOrd, written out: the entries of Mz inside the shapes of the
list are below 2^18 in size, all identities of the group vanish on the cells of Mz, and all entries
of the eight key vectors on them are images of entries of the library's reference tables. For both
forms hd of the head's cells: the bound holds at every place. -/
theorem linkOK_even (hd : Cm.Seg.Hd) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr)
    (sc : Scales) (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) (H : SmallM y Mz)
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
    L5.LinkOK hd (Cm.Seg.TS.segM (scalesOf h sc nf)) Wi x (2 * g) (libMZ y g Mz) :=
  L5.linkOK_of_holds
    (fun _ _ _ => (link_even hy S Z Z2 hp4 Mz Wi hg sc nf x H hI hV).1 _ _ _)
    (link_even hy S Z Z2 hp4 Mz Wi hg sc nf x H hI hV).2

/-- What link 2 g in order at libMZ y g Mz says on the cells of Mz: the identities and the key
vectors. Of the bound nothing is said back. -/
theorem linkOK_even_says (hd : Cm.Seg.Hd) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr)
    (sc : Scales) (nf : Inst.Model.NormPar) (x : Cm.Seg.XI)
    (L : L5.LinkOK hd (Cm.Seg.TS.segM (scalesOf h sc nf)) Wi x (2 * g) (libMZ y g Mz)) :
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
  (holds_mz_file hy S Z Z2 hp4 Mz Wi hg sc nf x).mp L.holds

/-- linkOK_even with the three hypotheses under their name. -/
theorem linkOK_layer (hd : Cm.Seg.Hd) {Mz : Mats ℤ} {Wi : Mat} {g : ℕ} (hg : g < nGr)
    {sc : Scales} (nf : Inst.Model.NormPar) {x : Cm.Seg.XI} (O : LayerOrd h sc y g Mz Wi x) :
    L5.LinkOK hd (Cm.Seg.TS.segM (scalesOf h sc nf)) Wi x (2 * g) (libMZ y g Mz) :=
  linkOK_even hy S Z Z2 hp4 hd Mz Wi hg sc nf x O.small O.idn O.key

/-- A group is in order at Mz exactly if the entries of Mz inside the shapes are small and link 2 g
is in order at the library's matrices made from Mz. An equivalence: the clauses are restated along
a renumbering of places, not derived. -/
theorem layerOrd_iff (hd : Cm.Seg.Hd) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr)
    (sc : Scales) (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) :
    LayerOrd h sc y g Mz Wi x ↔
      SmallM y Mz ∧
        L5.LinkOK hd (Cm.Seg.TS.segM (scalesOf h sc nf)) Wi x (2 * g) (libMZ y g Mz) :=
  ⟨fun O => ⟨O.small, linkOK_layer hy S Z Z2 hp4 hd hg nf O⟩,
    fun H => ⟨H.1, (linkOK_even_says hy S Z Z2 hp4 hd Mz Wi hg sc nf x H.2).1,
      (linkOK_even_says hy S Z Z2 hp4 hd Mz Wi hg sc nf x H.2).2⟩⟩

#print axioms linkOK_even
#print axioms linkOK_even_says
#print axioms linkOK_layer
#print axioms layerOrd_iff

end OnBytes.Road
