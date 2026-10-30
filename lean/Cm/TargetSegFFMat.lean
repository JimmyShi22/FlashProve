-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFMat.lean: the seven key families of the feed-forward segment that hold a matrix
product with weights, as families (`Fam`) of Cb/Req/ReqSpec.lean over p = 2^64 - 2^32 + 1: G, U
(gate and up projection; dense, shared and routed), QK (queries and keys, with the rotation), V, O,
D (down projection; with experts), LR (router).

Definitions and statements (`Cm.Seg.TS.Spec`: matKey_..); the proofs are in
Cm/TargetSegFFMatProofs.lean and Cm/TargetSegFFMatProofsA.lean to Cm/TargetSegFFMatProofsE.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex b < 2^v of a cube: a
sum of terms, each a coefficient (`Term.coef`: a function of the instance and the vertex) times a
product of atoms. An atom is an affine form in cells, an index atom, or the sum of such terms over
further variables (a sum atom). An index atom (`IdxAtom`) is a tensor form on the index matrix; the
model's weight tensors are written as such atoms in Cm/TargetSegIdxModel.lean. Used in `kfAll`
(Cm/TargetSegFFAll.lean).

The shape of such a key (Inst/Model/FF/Trace.lean: `key`; Inst/Model/Common/Site.lean: `ssite`).
The low key of a rounding q = rhu(A, k) is 2^dn(k) · A + [ 2^dn(k) · (2^(k-1) - 2^k q) - 2^16 rh ].
The bracket is affine in cells (`cLow`, Cm/SegFFMat.lean). A is a matrix product with weights
(`wpart` is 2^dn(k) · A):
  V, O, LR: ∑_j cell_j · W[j][x] (cell_j: the array's value at j): one block (`blk`,
    Cm/SegFFMatKit.lean: a sum atom with one monomial, that is one term, for each index atom): 13
    further variables for j.
  G, U: the same on dense layers and on the shared expert; on the routed expert
    ∑_e sel_e ∑_j xr_j · E[e][j][x - fe]: a second block, 7 + 13 further variables for (e, j),
    three atoms in a monomial.
  D: ∑_j sl_j · up_j · W_d[j][x] (14 further variables), and in a layer with experts
    ∑_e sel_e ∑_j sl_(fe+j) · up_(fe+j) · E_d[e][j][x]: four atoms in a monomial.
  QK: the rotation: C · AY[x] minus or plus S · AY[partner of x]. AY is read at x with its lowest
    bit replaced by the constant 0, and by the constant 1, with the coefficients `rot`.
Vertices as in Cm/SegPilotAff.lean: b = (ℓ | x | i): 2 bits, `vxOf s` bits, 10 bits; in a block
(b, j) ↦ b · 2^w + j. So variable 0, 1 = ℓ; 2, .., 1 + vx = x; then i; then the further variables.
Layers. The tensor of another layer is another index atom: a block has one monomial for each layer
(for each layer with experts; in QK two for each layer, one for each value of the replaced bit),
whose coefficient is 0 in the other layers.
Dead vertices (x beyond the length of the family; LR in a layer without experts): the affine part
is the padding value of the table, every coefficient of a block is 0 (`mblk`). A channel j beyond
the width of an array: the form is the constant 0 (`gVal`, Cm/SegFFMatKit.lean), so no place is
named there.

Stated, for all tables tb and every table of scales. `Spec.matKey_live` (V): for every group g < 12
and each of the seven families (`isMat s = true`), at the vertex of (ℓ, x, i) with ℓ < `DF.nl`, the
family present in ℓ, x below its length, i < `DF.T`, the value is `FFSeg.key`. `Spec.matKey_dead`
(D), `Spec.matKey_wf` (W): see their doc comments. `Spec.matKey_places` (P): the family reads only
places of valid cells that the segment reads, own or borrowed (`IsFF`). `Spec.matKey_ok`: for every
group g < 12 and each of the seven, `matKeyFam g tb s` has `KeyOK` of Cm/TargetSegFF.lean.

`isMat`, `cSs`, `mXS`, `cLow`, `lowForm`, `liv` are Cm/SegFFMat.lean's. The fields are `Cb.Gl.F`,
`Cb.Gl.E` (Cb/Gl/GlField.lean); the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).

Limits: this file says nothing on the other five families that are not affine (N1, N2, XR, DD, MR),
nothing on identities. The field and the format of the index are fixed (`Cb.Gl.E`, `fmtRef`); the
sizes are the reference ones (the index atoms of Cm/TargetSegIdxModel.lean).

Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFMat
import Cm.TargetSegAll
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegIdxModel
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass
noncomputable section -- Lean tags what it cannot compile


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All Finset
open Ex

variable [scl : Scl]

/-! ## The products -/

section Prod
variable {X : Type} (g : ℕ) (tb : Tables)

/-- a block of the family s: all coefficients are 0 at dead vertices -/
def mblk (s : FFSeg.Fam) (w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → Cb.Gl.E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm Cb.Gl.E)) (ia : ℕ → IdxAtom Cb.Gl.E) : Ex1 X Cb.Gl.E :=
  blk (vxOf s) w n (fun k l x i j => if liv s l x then c k l x i j else 0) fs ia

/-- the public weight 2^dn(k) of a product under the shift k -/
def wsc (k : ℕ) : Cb.Gl.E := 2 ^ Site.dn k

/-- the public coefficient of the rotation in layer L at (x, i), for AY at x with the lowest bit β:
(C, -S) at even x, (S, C) at odd x -/
def rot (L x i β : ℕ) : Cb.Gl.E :=
  if (x % DF.P.ch) % 2 = 0 then
    (if β = 0 then ((tb.C L i ((x % DF.P.ch) / 2) : ℤ) : Cb.Gl.E)
      else -((tb.S L i ((x % DF.P.ch) / 2) : ℤ) : Cb.Gl.E))
  else
    (if β = 0 then ((tb.S L i ((x % DF.P.ch) / 2) : ℤ) : Cb.Gl.E)
      else ((tb.C L i ((x % DF.P.ch) / 2) : ℤ) : Cb.Gl.E))

/-- The product with weights, under its public weight. -/
def wpart : FFSeg.Fam → Ex1 X Cb.Gl.E
  | .V =>
    mblk .V 13 4 (fun k l _ _ _ => if l = k then wsc (DF.Pl l).kv else 0)
      [fun l _ i j => gVal g .a l j i] fun k => aV (4 * g + k) (Src.run 22 13) (Src.run 2 10)
  | .O =>
    mblk .O 13 4 (fun k l _ _ _ => if l = k then wsc (DF.Pl l).ko else 0)
      [fun l _ i j => gVal g .o l j i] fun k => aO (4 * g + k) (Src.run 25 13) (Src.run 2 13)
  | .LR =>
    mblk .LR 13 2 (fun k l _ _ _ => if l = 2 * k + 1 then wsc (DF.Pl l).kr else 0)
      [fun l _ i j => gVal g .m l j i]
      fun k => aR (4 * g + (2 * k + 1)) (Src.run 19 13) (Src.run 2 7)
  | .G =>
      mblk .G 13 4
        (fun k l x _ _ =>
          if l = k then (if FFSeg.routed DF l x then 0 else wsc (FFSeg.kG DF l x)) else 0)
        [fun l _ i j => gVal g .m l j i] (fun k => aG (4 * g + k) (Src.run 26 13) (Src.run 2 14))
      + mblk .G 20 2
        (fun k l x _ _ =>
          if l = 2 * k + 1 then (if FFSeg.routed DF l x then wsc (FFSeg.kG DF l x) else 0) else 0)
        [fun l _ i j => cVal g .sel (l / 2) (j / 2 ^ 13) i,
          fun l _ i j => gVal g .xr (l / 2) (j % 2 ^ 13) i]
        (fun k => aEg (4 * g + (2 * k + 1)) (Src.run 33 13) (Src.run 26 7) (Src.run 3 13))
  | .U =>
      mblk .U 13 4
        (fun k l x _ _ =>
          if l = k then (if FFSeg.routed DF l x then 0 else wsc (FFSeg.kU DF l x)) else 0)
        [fun l _ i j => gVal g .m l j i] (fun k => aU (4 * g + k) (Src.run 26 13) (Src.run 2 14))
      + mblk .U 20 2
        (fun k l x _ _ =>
          if l = 2 * k + 1 then (if FFSeg.routed DF l x then wsc (FFSeg.kU DF l x) else 0) else 0)
        [fun l _ i j => cVal g .sel (l / 2) (j / 2 ^ 13) i,
          fun l _ i j => gVal g .xr (l / 2) (j % 2 ^ 13) i]
        (fun k => aEu (4 * g + (2 * k + 1)) (Src.run 33 13) (Src.run 26 7) (Src.run 3 13))
  | .D =>
      mblk .D 14 4 (fun k l _ _ _ => if l = k then wsc (DF.Pl l).kd else 0)
        [fun l _ i j => cVal g .sl l j i, fun l _ i j => cVal g .up l j i]
        (fun k => aD (4 * g + k) (Src.run 25 14) (Src.run 2 13))
      + mblk .D 20 2 (fun k l _ _ _ => if l = 2 * k + 1 then wsc (DF.Pl l).kd else 0)
        [fun l _ i j => cVal g .sel (l / 2) (j / 2 ^ 13) i,
          fun l _ i j => cVal g .sl l (DF.fe + j % 2 ^ 13) i,
          fun l _ i j => cVal g .up l (DF.fe + j % 2 ^ 13) i]
        (fun k => aEd (4 * g + (2 * k + 1)) (Src.run 32 13) (Src.run 25 7) (Src.run 2 13))
  | .QK =>
    mblk .QK 13 (4 * 2)
      (fun k l x i _ =>
        if l = k / 2 then wsc (FFSeg.kQK DF l x) * rot tb (4 * g + l) x i (k % 2) else 0)
      [fun l _ i j => gVal g .a l j i]
      fun k => aQK (4 * g + k / 2) (Src.run 2 12 ++ [.bit (k % 2 == 1)]) (Src.run 25 13)
  | _ => Ex.zero

/-- the key as an expression -/
def matKeyE (s : FFSeg.Fam) : Ex1 X Cb.Gl.E := aff (lowForm g tb s) + wpart g tb s

/-- The family. -/
def matKeyFam (s : FFSeg.Fam) : Cb.Fam X Cb.Gl.E :=
  Ex1.fam (2 + vxOf s + 10) (matKeyE g tb s)

end Prod
end Cm.Seg.TS

namespace Cm.Seg.TS.Spec
open Cm.Spec
open Cb Code Inst.Model Inst.Model.All Cm.Seg

/-- (V) States: for g < `nGr` and each of the seven families, at the vertex of an index (ℓ, x, i)
of the family, the family's value is the key of Inst/Model/FF/Trace.lean, over `Cb.Gl.E`, at the
matrices read as a trace and the weights read from the index matrix; for all matrices. -/
def matKey_live : Prop :=
  ∀ [Scl] (X : Type) (g : ℕ) (tb : Tables) (s : FFSeg.Fam), g < nGr → isMat s = true →
    ∀ (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (l x i : ℕ), l < DF.nl →
      FFSeg.present s l = true → x < FFSeg.len DF s → i < DF.T →
      (matKeyFam (X := X) g tb s).val fmtRef x₀ W A (enc3 (vxOf s) l x i) =
        FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) s l x i

/-- (D) States: at a dead vertex the family's value is the padding value of the table. -/
def matKey_dead : Prop :=
  ∀ [Scl] (X : Type) (g : ℕ) (tb : Tables) (s : FFSeg.Fam) (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F)
      (A : ℕ → ℕ → ℕ → Cb.Gl.E) (b : ℕ),
    ¬ Live s b → (matKeyFam (X := X) g tb s).val fmtRef x₀ W A b = ((padOf tb s : ℤ) : Cb.Gl.E)

/-- (W) States: the family is well formed (`Fam.WF`, Cb/Req/ReqSpec.lean) at `fmtRef`. -/
def matKey_wf : Prop :=
  ∀ [Scl] (X : Type) (g : ℕ) (tb : Tables) (s : FFSeg.Fam), (matKeyFam (X := X) g tb s).WF fmtRef

/-- (P) States: the places read are places of valid cells that the segment reads. -/
def matKey_places : Prop :=
  ∀ [Scl] (X : Type) (g : ℕ) (tb : Tables) (s : FFSeg.Fam),
    ∀ p ∈ (matKeyFam (X := X) g tb s).places, IsFF g p

/-- States: for g < `nGr`, each of the seven families has what the theorems on `ffSpec` require of
a family of keys (`KeyOK`, Cm/TargetSegFF.lean). -/
def matKey_ok : Prop :=
  ∀ [Scl] (X : Type) (g : ℕ) (tb : Tables) (s : FFSeg.Fam),
    g < nGr → isMat s = true → KeyOK fmtRef g tb s (matKeyFam (X := X) g tb s)

end Cm.Seg.TS.Spec
