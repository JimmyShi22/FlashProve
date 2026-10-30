-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegIdxModel.lean: the weight tensors of the model as index atoms over p = 2^64 - 2^32 + 1,
at the reference sizes and layout.

Definitions and statements; proofs: Cm/TargetSegIdxModelProofs.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). An index atom (`IdxAtom` with its law `IdxAtom.OK`,
Cb/Req/ReqSpec.lean) is a vector on the vertices of a cube, linear in the index matrix, whose
multilinear extension at every point is a tensor form: through such atoms the conditions read the
model's weights. In this file a vertex is called dead if the indices that it encodes are outside
the shape of the model's tensor (for `aQK`: x ≥ 6,144 or j ≥ 5,120). The atoms are used in the
families of Cm/TargetSegFFMat.lean (`aQK` to `aEd`), Cm/TargetSegFFCellIdnOK.lean (`aEmb`) and
Cm/TargetSegHead.lean (`aH`).

`fOf` is Cm/SegIdxModel.lean's: it names no field.
The fields are `Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).

The atoms. Each takes, for every index of the tensor, the sources of its bits (Cm/SegIdx.lean:
variables of the family's cube, negated variables, constants), most significant first; variables
that no source names are not read.
  `aQK L σx σj`: queries and keys of layer L in one: x = 128 · head + channel has 13 bits; heads 0
    .. 39 are the query heads, 40 .. 47 the key heads (so x < 5,120 reads W_q[j][x], and 5,120 ≤ x
    < 6,144 reads W_k[j][x - 5,120]); heads 48 .. 63 hold no weight.
  `aV`, `aO`, `aG`, `aU`, `aD`: values, output projection, gate, up, down (in a layer with experts:
    of the shared expert). σj: the input index, σx: the output index.
  `aR`: router (layers with experts). σj, σe.
  `aEg`, `aEu`, `aEd`: gate, up, down of the routed experts (layers with experts). σj, σe, σx.
  `aEmb σt σj`: embedding: token (18 bits), channel; four digits. `aH σv σj`: output matrix: token
    (18 bits), channel.

Main names:
  `Spec.ok2`, `Spec.ok3`, `Spec.qk_ok`, `Spec.tok_ok`: each atom has the law of an index atom
    (`IdxAtom.OK`) on v variables, if no variable is named twice and all are below v, and the lists
    are long enough (in `qk_ok` σx has exactly 13 sources, in `tok_ok` σt exactly 18). `ok2`, `ok3`
    are stated of every unit with two or three coordinates, none of kind whole, each of positive
    size.
  `Spec.v_vtx` to `Spec.ed_vtx`: for L < 48 (for `r_vtx'`, `eg_vtx`, `eu_vtx`, `ed_vtx`: a layer
    with experts, `hasExperts L`) and lists that are long enough, at every vertex the atom is the
    image in `Cb.Gl.E` of the entry of the matrix of the layer as the conditions of
    Inst/Model/FF/Trace.lean read it from the index matrix W over the field
    (`FFSeg.layerR ppref kRef W L`), which is 0 outside the tensor's shape.

Limits: three atoms have dead vertices at which they are not 0 (as functions of the index matrix
W), so their statements at a vertex have one hypothesis more: `Spec.qk_vtx` (x < 6,144),
`Spec.emb_vtx` and `Spec.h_vtx` (token < 202,048). Beyond, the atom reads entries of the index
matrix at which no weight lies. A family that uses them needs a coefficient table that is 0 there.
The three also have L < 48 (`qk_vtx`), σx of 13 bits, σt and σv of 18 bits, and σj long enough.
That the matrix read off a message that holds the index i is (1) the matrix read off
the honest message of i and (2) the image of i's integer matrix is not stated in this file.
Its second half is not proved in this library; in the terms of a partition it is the clause `idx`
of a partition's laws (Cb/Part/LdPartDef.lean).
The first half is not stated there.
This file says nothing on cells; no family is written here.

How the conditions of Inst/Model/ read the index, as far as read (by reading, not by a theorem).
Read whole: the definitions `key`, `idnVal` and `trace` of Inst/Model/FF/Trace.lean with the
abbreviations that they use. Read by their types only: the clauses of `Cm.TP.Cond`
(Cm/TargetPRel.lean).
  Feed-forward segments (which hold all projections of a layer): the matrix W enters only as
    `FFSeg.layerR ppref kRef W (L0 + l)` in the keys and as `FFSeg.embR ppref kRef W` in the
    identity (J11). There: (1) sums over j of a cell value, or a product of two, times an entry of
    a matrix of the layer; for the routed experts a sum over (e, j) of sel_e · cell_j (in the down
    projection a product of two) · entry; (2) the rotation: the product at x and at its partner, x
    with the lowest bit flipped (a negated variable), with public coefficients (`wpart` at `.QK`,
    Cm/TargetSegFFMat.lean, reads both with the lowest bit a constant, `.bit`); (3) the embedding at
    the token of a position, Emb[tok_i][j]: a sum over all tokens t of the public coefficient
    [t = tok_i], a function of the instance, times Emb[t][j]. These are sums of products of index
    atoms with cells and public coefficients.
  Attention segments: their clauses have no argument W. The head: its clauses are given W only as
    `castH W`, the image of `Layout.weightsOf`'s H (`Spec.h_int`); how the head's keys use H[j][v]
    was not read here.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegIdxModel
import Cm.TargetSegAll
noncomputable section -- Lean tags what it cannot compile


set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Blocks Finset Code Inst.Model Inst.Model.Layout

/-- the atom of the unit number n at the reference sizes -/
def rAtom (n : ℕ) (U : UnitS) (σs : List (List Src)) : IdxAtom Cb.Gl.E :=
  tAtom ppref kRef n U σs

section Atoms
variable (L : ℕ)

def aQK (σx σj : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L) (uQK ppref) [σx.take 6, σx.drop 6, σj]
def aV (σj σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 1) (uV ppref) [σj, σx]
def aO (σj σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 2) (uO ppref) [σj, σx]
def aG (σj σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 3) (uGU ppref (fOf L)) [σj, σx]
def aU (σj σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 4) (uGU ppref (fOf L)) [σj, σx]
def aD (σj σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + (if hasExperts L then 7 else 5)) (uD ppref (fOf L)) [σj, σx]
def aR (σj σe : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 9) (uR ppref) [σj, σe]
def aEg (σj σe σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 5) (uGUr ppref) [σj, σe, σx]
def aEu (σj σe σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 6) (uGUr ppref) [σj, σe, σx]
def aEd (σj σe σx : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref L + 8) (uDr ppref) [σj, σe, σx]

end Atoms

def aEmb (σt σj : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref ppref.layers) (uEmb ppref) [σt, σj]
def aH (σv σj : List Src) : IdxAtom Cb.Gl.E :=
  rAtom (first ppref ppref.layers + 1) (uH ppref) [σv, σj]

namespace Spec

def r_ok : Prop :=
  ∀ (v n : ℕ) (U : UnitS) (σs : List (List Src)),
    WidthsOK U.coords σs → Src.OK σs.flatten v → (rAtom n U σs).OK fmtRef v

open Classical in
def r_vtx : Prop :=
  ∀ (v n : ℕ) (U : UnitS) (σs : List (List Src)), (units ppref)[n]? = some U →
    WidthsOK U.coords σs →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (rAtom n U σs).at fmtRef W (vtx v b) =
      if InRows U.coords kRef (numsAt σs v b) then
        algebraMap Cb.Gl.F Cb.Gl.E (entryW ppref kRef W n U (numsAt σs v b))
      else 0

/-- a unit with two coordinates, none of kind whole: the matrix, 0 outside its shape. (not all
hypotheses are named here: see the statement below) -/
def vtx2 : Prop :=
  ∀ (v n R₁ R₂ nU : ℕ) (k₁ k₂ : Kind) (σ₁ σ₂ : List Src), k₁ ≠ .whole → k₂ ≠ .whole →
    (units ppref)[n]? = some ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩], nU⟩ → 0 < R₁ → 0 < R₂ →
    R₁ ≤ 2 ^ σ₁.length → R₂ ≤ 2 ^ σ₂.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ),
      (rAtom n ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩], nU⟩ [σ₁, σ₂]).at fmtRef W (vtx v b) =
        algebraMap Cb.Gl.F Cb.Gl.E
          (FFSeg.matR R₁ R₂
            (fun j x => FFSeg.entryR ppref kRef W n ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩], nU⟩ [j, x])
            (Src.num σ₁ v b) (Src.num σ₂ v b))

/-- as `vtx2`, for three coordinates, none of kind whole. (not all hypotheses are named here: see
the statement below) -/
def vtx3 : Prop :=
  ∀ (v n R₁ R₂ R₃ nU : ℕ) (k₁ k₂ k₃ : Kind) (σ₁ σ₂ σ₃ : List Src), k₁ ≠ .whole → k₂ ≠ .whole →
    k₃ ≠ .whole → (units ppref)[n]? = some ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩, ⟨R₃, k₃⟩], nU⟩ → 0 < R₁ → 0 < R₂ →
    0 < R₃ → R₁ ≤ 2 ^ σ₁.length → R₂ ≤ 2 ^ σ₂.length → R₃ ≤ 2 ^ σ₃.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ),
      (rAtom n ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩, ⟨R₃, k₃⟩], nU⟩ [σ₁, σ₂, σ₃]).at fmtRef W (vtx v b) =
        algebraMap Cb.Gl.F Cb.Gl.E
          (if Src.num σ₂ v b < R₂ then
              FFSeg.matR R₁ R₃
                (fun j x =>
                  FFSeg.entryR ppref kRef W n
                    ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩, ⟨R₃, k₃⟩], nU⟩ [j, Src.num σ₂ v b, x])
                (Src.num σ₁ v b) (Src.num σ₃ v b)
            else 0)

/-- the law of an index atom, for units with two and with three coordinates none of which is of
kind whole. (not all hypotheses are named here: see the statement below) -/
def ok2 : Prop :=
  ∀ (v n R₁ R₂ nU : ℕ) (k₁ k₂ : Kind) (σ₁ σ₂ : List Src), k₁ ≠ .whole → k₂ ≠ .whole → 0 < R₁ →
    0 < R₂ → R₁ ≤ 2 ^ σ₁.length → R₂ ≤ 2 ^ σ₂.length → Src.OK (σ₁ ++ σ₂) v →
    (rAtom n ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩], nU⟩ [σ₁, σ₂]).OK fmtRef v
def ok3 : Prop :=
  ∀ (v n R₁ R₂ R₃ nU : ℕ) (k₁ k₂ k₃ : Kind) (σ₁ σ₂ σ₃ : List Src), k₁ ≠ .whole → k₂ ≠ .whole →
    k₃ ≠ .whole → 0 < R₁ → 0 < R₂ → 0 < R₃ → R₁ ≤ 2 ^ σ₁.length → R₂ ≤ 2 ^ σ₂.length →
    R₃ ≤ 2 ^ σ₃.length → Src.OK (σ₁ ++ σ₂ ++ σ₃) v →
    (rAtom n ⟨[⟨R₁, k₁⟩, ⟨R₂, k₂⟩, ⟨R₃, k₃⟩], nU⟩ [σ₁, σ₂, σ₃]).OK fmtRef v
def qk_ok : Prop :=
  ∀ (v L : ℕ) (σx σj : List Src),
    σx.length = 13 → 5120 ≤ 2 ^ σj.length → Src.OK (σx ++ σj) v → (aQK L σx σj).OK fmtRef v
/-- embedding and output matrix -/
def tok_ok : Prop :=
  ∀ (v : ℕ) (σt σj : List Src), σt.length = 18 → 5120 ≤ 2 ^ σj.length → Src.OK (σt ++ σj) v →
    (aEmb σt σj).OK fmtRef v ∧ (aH σt σj).OK fmtRef v

/-! the tensors of a layer, as the conditions read the layer from W (`FFSeg.layerR`) -/

def qk_vtx : Prop :=
  ∀ (v L : ℕ) (σx σj : List Src), L < 48 → σx.length = 13 → 5120 ≤ 2 ^ σj.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), Src.num σx v b < 6144 →
      (aQK L σx σj).at fmtRef W (vtx v b) =
        algebraMap Cb.Gl.F Cb.Gl.E
          (if Src.num σx v b < 5120 then
              (FFSeg.layerR ppref kRef W L).Wq (Src.num σj v b) (Src.num σx v b)
            else (FFSeg.layerR ppref kRef W L).Wk (Src.num σj v b) (Src.num σx v b - 5120))
def v_vtx : Prop :=
  ∀ (v L : ℕ) (σj σx : List Src), L < 48 → 5120 ≤ 2 ^ σj.length → 1024 ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aV L σj σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Wv (Src.num σj v b) (Src.num σx v b))
def o_vtx : Prop :=
  ∀ (v L : ℕ) (σj σx : List Src), L < 48 → 5120 ≤ 2 ^ σj.length → 5120 ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aO L σj σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Wo (Src.num σj v b) (Src.num σx v b))
def g_vtx : Prop :=
  ∀ (v L : ℕ) (σj σx : List Src), L < 48 → 5120 ≤ 2 ^ σj.length → fOf L ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aG L σj σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Wg (Src.num σj v b) (Src.num σx v b))
def u_vtx : Prop :=
  ∀ (v L : ℕ) (σj σx : List Src), L < 48 → 5120 ≤ 2 ^ σj.length → fOf L ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aU L σj σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Wu (Src.num σj v b) (Src.num σx v b))
def d_vtx : Prop :=
  ∀ (v L : ℕ) (σj σx : List Src), L < 48 → fOf L ≤ 2 ^ σj.length → 5120 ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aD L σj σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Wd (Src.num σj v b) (Src.num σx v b))
def r_vtx' : Prop :=
  ∀ (v L : ℕ) (σj σe : List Src), L < 48 → hasExperts L →
    5120 ≤ 2 ^ σj.length → 128 ≤ 2 ^ σe.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aR L σj σe).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Wr (Src.num σj v b) (Src.num σe v b))
def eg_vtx : Prop :=
  ∀ (v L : ℕ) (σj σe σx : List Src), L < 48 → hasExperts L → 5120 ≤ 2 ^ σj.length →
    128 ≤ 2 ^ σe.length → 8192 ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aEg L σj σe σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Eg (Src.num σe v b) (Src.num σj v b) (Src.num σx v b))
def eu_vtx : Prop :=
  ∀ (v L : ℕ) (σj σe σx : List Src), L < 48 → hasExperts L → 5120 ≤ 2 ^ σj.length →
    128 ≤ 2 ^ σe.length → 8192 ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aEu L σj σe σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Eu (Src.num σe v b) (Src.num σj v b) (Src.num σx v b))
def ed_vtx : Prop :=
  ∀ (v L : ℕ) (σj σe σx : List Src), L < 48 → hasExperts L → 8192 ≤ 2 ^ σj.length →
    128 ≤ 2 ^ σe.length → 5120 ≤ 2 ^ σx.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), (aEd L σj σe σx).at fmtRef W (vtx v b) =
      algebraMap Cb.Gl.F Cb.Gl.E
        ((FFSeg.layerR ppref kRef W L).Ed (Src.num σe v b) (Src.num σj v b) (Src.num σx v b))
def emb_vtx : Prop :=
  ∀ (v : ℕ) (σt σj : List Src), σt.length = 18 → 5120 ≤ 2 ^ σj.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), Src.num σt v b < 202048 →
      (aEmb σt σj).at fmtRef W (vtx v b) =
        algebraMap Cb.Gl.F Cb.Gl.E (FFSeg.embR ppref kRef W (Src.num σt v b) (Src.num σj v b))
def h_vtx : Prop :=
  ∀ (v : ℕ) (σv σj : List Src), σv.length = 18 → 5120 ≤ 2 ^ σj.length →
    ∀ (W : ℕ → ℕ → Cb.Gl.F) (b : ℕ), Src.num σv v b < 202048 →
      (aH σv σj).at fmtRef W (vtx v b) =
        algebraMap Cb.Gl.F Cb.Gl.E
          (FFSeg.matR ppref.d ppref.V
            (fun j t => FFSeg.entryR ppref kRef W (first ppref ppref.layers + 1) (uH ppref) [t, j])
            (Src.num σj v b) (Src.num σv v b))
/-- the output matrix as the head's conditions read it, for an integer matrix -/
def h_int : Prop :=
  ∀ (M : Mat) (j t : ℕ),
    FFSeg.matR ppref.d ppref.V
        (fun j t =>
          FFSeg.entryR ppref kRef (fun y c => ((M y c : ℤ) : Cb.Gl.F))
            (first ppref ppref.layers + 1) (uH ppref) [t, j])
        j t =
      (((weightsOf ppref kRef M).H j t : ℤ) : Cb.Gl.F)

end Spec
end Cm.Seg.TS
