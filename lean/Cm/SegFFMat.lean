-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFMat.lean: what the seven key families of the feed-forward segment that hold a matrix product
with weights have in common, for any field: G, U (gate and up projection; dense, shared and routed),
QK (queries and keys, with the rotation), V, O, D (down projection; with experts), LR (router).

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex b < 2^v of a cube: a
sum of terms, each a coefficient (`Term.coef`: a function of the instance and the vertex) times a
product of atoms. An atom is an affine form in cells, an index atom, or the sum of such terms over
further variables (a sum atom). An index atom (`IdxAtom`) is a tensor form on the index matrix; the
model's weight tensors are written as such atoms in Cm/TargetSegIdxModel.lean.

Definitions; the lemmas are in Cm/SegFFMatProofs.lean, Cm/SegFFMatProofsB.lean,
Cm/SegFFMatProofsD.lean and Cm/SegFFMatProofsE.lean; the families, over `Cb.Gl.E`:
Cm/TargetSegFFMat.lean.

Limits: this file says nothing on the other five families that are not affine (N1, N2, XR, DD, MR),
nothing on identities. The format of the index and the sizes are the reference ones (the index atoms
of Cm/TargetSegIdxModel.lean).

The shape of such a key (Inst/Model/FF/Trace.lean: `key`; Inst/Model/Common/Site.lean: `ssite`).
The low key of a rounding q = rhu(A, k) is 2^dn(k) · A + [ 2^dn(k) · (2^(k-1) - 2^k q) - 2^16 rh ].
The bracket is affine in cells (`cLow`). A is a matrix product with weights, written in blocks
(`blk`, Cm/SegFFMatKit.lean: a sum atom with one monomial, that is one term, for each index atom);
family by family, with layers and dead vertices: the head of Cm/TargetSegFFMat.lean.
Vertices as in Cm/SegPilotAff.lean: b = (ℓ | x | i): 2 bits, `vxOf s` bits, 10 bits; in a block
(b, j) ↦ b · 2^w + j. So variable 0, 1 = ℓ; 2, .., 1 + vx = x; then i; then the further variables.

Statements on places, values, well-formedness and `KeyOK`: `Cm.Seg.TS.Spec`
(Cm/TargetSegFFMat.lean), of the families `Cm.Seg.TS.matKeyFam` over `Cb.Gl.E`.
Main names: `isMat`, `cSs`, `mXS`, `cLow`, `lowForm`, `liv`; Cm/TargetSegFFMat.lean reads them.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFMatKit
import Cm.SegFF
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset
open Ex

variable [scl : Scl]

/-- The families with a matrix product with weights. -/
def isMat : FFSeg.Fam → Bool
  | .G | .U | .QK | .O | .D | .V | .LR => true
  | _ => false

/-! ## The affine part -/

section Low
variable {E : Type} [Field E] (g : ℕ)

/-- the low key of a rounding without its product: ssite 0 q rh k, as a form -/
def cSs (q rh : CForm E) (k : ℕ) : CForm E :=
  ((2 : E) ^ Site.dn k) • (cK (2 ^ (k - 1)) - ((2 : E) ^ k) • q) - ((2 : E) ^ 16) • rh

/-- the stream at the place s, as a form -/
def mXS (s j i : ℕ) : CForm E := cVal g (FFSeg.streamAt DF s).1 (FFSeg.streamAt DF s).2 j i

/-- The affine part of the key. -/
def cLow : FFSeg.Fam → ℕ → ℕ → ℕ → CForm E
  | .G, l, x, i =>
    cSs (cVal g .g0 l x i + (256 : E) • cVal g .gh l x i) (cVal g .rg l x i) (FFSeg.kG DF l x)
  | .U, l, x, i => cSs (cVal g .up l x i) (cVal g .ru l x i) (FFSeg.kU DF l x)
  | .QK, l, x, i => cSs (cVal g .qkw l x i) (cVal g .rqk l x i) (FFSeg.kQK DF l x)
  | .O, l, x, i => cSs (mXS g (2 * l + 1) x i - mXS g (2 * l) x i) (cVal g .ro l x i) (DF.Pl l).ko
  | .D, l, x, i =>
    cSs (mXS g (2 * l + 2) x i - mXS g (2 * l + 1) x i) (cVal g .rd l x i) (DF.Pl l).kd
  | .V, l, x, i => cSs (cVal g .vw l x i) (cVal g .rv l x i) (DF.Pl l).kv
  | .LR, l, x, i =>
    cSs ((8 : E) • cVal g .ly (l / 2) x i + cVal g .l3 (l / 2) x i)
      (cVal g .rl (l / 2) x i) (DF.Pl l).kr
  | _, _, _, _ => cK 0

/-- the affine part at a vertex: at a dead vertex the padding value of the table -/
def lowForm (tb : Tables) (s : FFSeg.Fam) (b : ℕ) : CForm E :=
  if Live s b then cLow g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2
  else cK ((padOf tb s : ℤ) : E)

end Low

/-! ## The indices of a family -/

section Prod
/-- (ℓ, x) is an index of the family -/
def liv (s : FFSeg.Fam) (l x : ℕ) : Prop := x < FFSeg.len DF s ∧ FFSeg.present s l = true

instance (s : FFSeg.Fam) (l x : ℕ) : Decidable (liv s l x) := by unfold liv; infer_instance

end Prod
end Cm.Seg
