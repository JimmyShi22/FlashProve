-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFAll.lean: the feed-forward segment of group g (all of the group's four layers but
attention itself, from queries, keys and values to its output o (Cm/TargetSegAtt.lean); 34 families
of keys, among them the seven that hold a matrix product with weights: queries and keys with the
rotation, values, output projection, gate, up and down projections with the routed experts, router;
see the head of Cm/TargetSegModel.lean), with all its families, over p = 2^64 - 2^32 + 1: the
segment `ffSpec` of Cm/TargetSegFF.lean with nothing left as a parameter.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

Definitions and statements (`Cm.Seg.TS.Spec`); proofs: Cm/TargetSegFFAllProofs.lean.

A segment (`SegSpec`, Cb/Req/ReqSpec.lean) has the shape of its matrix of cells, its families of
identities and its families of keys with their tables. Group g is four consecutive layers of the
model. Used as segment 2 g of the model (`segOf`, Cm/TargetSegModelOf.lean).

Main names:
  `kfAll g tb s`: the family that renders the keys of s: the affine one (22 families,
    Cm/SegPilotAff.lean), the one with products of cells (5, Cm/SegFFCellKeys.lean), or the one
    with a matrix product with weights (7, Cm/TargetSegFFMat.lean).
  `ffSeg κ nf g tok`: the segment at the words κ (`LayerScale`) of the layers: 2^19 rows, 5,990
    columns; the 34 families of keys with their tables; the identities (J1) to (J10), and (J11) for
    g = 0. tok reads the prompt off the instance.
Stated, for g < 12, over `Cb.Gl.E` at the format `Cm.Seg.TS.fmtRef`:
  `ffSeg_toMat`: for `h.OK`, for the matrices of a trace: the segment's conditions hold if and only
    if the clauses `ffKey` and `ffIdn` of the model's conditions (Cm/TargetPRel.lean: `TP.CondL` at
    `Cb.Gl.p`) hold at g (completeness).
  `ffSeg_ofMat`: for all integer matrices M: they hold at M if and only if these clauses hold at g
    for the trace of M (knowledge soundness).
  `ffSeg_wf`, `ffSeg_reads`: the segment is well formed; it reads only places that the layout lists
    for segment 2 g.
  `kfAll_ok`: every family of keys has `KeyOK` (Cm/TargetSegFF.lean).

The fields are `Cb.Gl.F`,
`Cb.Gl.E` (Cb/Gl/GlField.lean); the
format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).
`castW` is `Cm.TP.castW Cb.Gl.p` (an integer index matrix,
read modulo p) and `segFF κ nf g` is `Cm.TP.segFF Cb.Gl.p κ nf g`: the model's conditions are
`Cm.TP.CondL` at `Cb.Gl.p` (Cm/TargetPRel.lean: clauses `ffKey`, `ffIdn`).


Limits: this file says nothing on bounds of cells, on the other segments, on any protocol. The
index matrix is the image of an integer matrix (this is not proved in this library, for a
message that holds an index).




Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFMat
import Cm.SegFFCellKeys
import Cm.SegFFCellIdnOK
import Cm.TargetSegAll
import Cm.TargetSegFFMat
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegIdxModel
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass
import Cm.TargetSegFFCellKeys
import Cm.TargetSegFFCellIdnOK
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All

/-- The family of the keys of s. -/
def kfAll [scl : Scl] {X : Type} (g : ℕ) (tb : Tables) (s : FFSeg.Fam) :
    Cb.Fam X Cb.Gl.E :=
  if isAff s then affKeyFam g tb s else if isQuad s then quadKeyFam g tb s else matKeyFam g tb s

/-- The feed-forward segment of group g (what the name covers: this file's head) at the words κ
(`LayerScale`) of the layers. -/
def ffSeg {X : Type} (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ) (tok : X → ℕ → ℕ) :
    SegSpec X Cb.Gl.F Cb.Gl.E :=
  ffSpec tbRef (kfAll (scl := SFK κ nf g) g tbRef) (idnFams (scl := SFK κ nf g) g tok)

end Cm.Seg.TS

namespace Cm.Seg.TS.Spec
open Cm.Spec
open Cb Code Inst.Model Inst.Model.All Cm.Seg

/-- States: for g < `nGr`, every family of keys has what the theorems on `ffSpec` require
(`KeyOK`). -/
def kfAll_ok : Prop :=
  ∀ [Scl] (X : Type) (g : ℕ) (tb : Tables) (s : FFSeg.Fam),
    g < nGr → KeyOK fmtRef g tb s (kfAll (X := X) g tb s)

def ffSeg_toMat : Prop :=
  ∀ (X : Type) (κ : ℕ → LayerScale) (nf : NormPar) (h : Hd) (g : ℕ) (tok : X → ℕ → ℕ), h.OK →
    g < nGr →
    ∀ (x₀ : X) (T : Trace) (Wi : Mat),
      (ffSeg κ nf g tok).Holds fmtRef x₀ (TP.castW Cb.Gl.p Wi)
        (Partition.castM (E := Cb.Gl.E) (toMat h T)) ↔
      (∀ k, (TP.segFF Cb.Gl.p κ nf g).key
          (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => T.vFF g c.val) k ∈
        (TP.segFF Cb.Gl.p κ nf g).table k) ∧
      ∀ j,
        (TP.segFF Cb.Gl.p κ nf g).idn (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => T.vFF g c.val) j = 0

def ffSeg_ofMat : Prop :=
  ∀ (X : Type) (κ : ℕ → LayerScale) (nf : NormPar) (h : Hd) (g : ℕ) (tok : X → ℕ → ℕ), g < nGr →
    ∀ (x₀ : X) (M : ℕ → ℕ → ℕ → ℤ) (Wi : Mat),
      (ffSeg κ nf g tok).Holds fmtRef x₀ (TP.castW Cb.Gl.p Wi) (Partition.castM (E := Cb.Gl.E) M) ↔
      (∀ k, (TP.segFF Cb.Gl.p κ nf g).key
          (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => (ofMat h M).vFF g c.val) k ∈
        (TP.segFF Cb.Gl.p κ nf g).table k) ∧
      ∀ j, (TP.segFF Cb.Gl.p κ nf g).idn
          (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => (ofMat h M).vFF g c.val) j = 0

def ffSeg_wf : Prop :=
  ∀ (X : Type) (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ) (tok : X → ℕ → ℕ),
    g < nGr → (ffSeg κ nf g tok).WF fmtRef

def ffSeg_reads : Prop :=
  ∀ (X : Type) (κ : ℕ → LayerScale) (nf : NormPar) (h : Hd) (g : ℕ) (tok : X → ℕ → ℕ),
    g < nGr → ∀ p ∈ (ffSeg κ nf g tok).places, p ∈ reads h (2 * g)

end Cm.Seg.TS.Spec
