-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdxTensor.lean: the index atom of a weight tensor, from the sources of the bits of its
indices: the form in which the families of a segment use Cm/SegIdx.lean.

Definitions and statements; proofs: Cm/SegIdxTensorProofs.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). An index atom (`IdxAtom` with its law `IdxAtom.OK`,
Cb/Req/ReqSpec.lean) is a vector on the vertices of a cube, linear in the index matrix, whose
multilinear extension at every point is a tensor form: through such atoms the model's conditions
read the weights. A source (`Src`, Cm/SegIdx.lean) says where a bit comes from: a variable of the
cube, its negation, or a constant. A unit (`UnitS`, Inst/Model/Layout.lean) is one weight tensor
with its coordinates, as the layout puts it into the index matrix.

Main names:
  `tAtom P k n U σs`: the atom of the unit U, which has the number n in the order of the layout; σs
    holds, for each coordinate of the unit, the sources of all bits of that index, most significant
    first. Which of these bits are column bits and which row bits is computed from the layout
    (`cutBits`).
  `WidthsOK U.coords σs`: one list for each coordinate, each with `WidthOK`.
  `InRows cs left is`: every index is inside its coordinate, but for the coordinates that lie
    wholly in the column bits (kind whole with column bits), of which nothing is asked.

Stated (`Spec`); `t_ok` and `t_vtx` both for k = the number of column bits of the format
(Φ.hi + Φ.lo):
  `t_ok`: `WidthsOK`, no variable named twice, all below v ⇒ the law of an index atom
    (`IdxAtom.OK`) on v variables.
  `t_vtx`: under `WidthsOK`, if the unit's rows are inside the matrix: at the vertex b the atom is
    the image in E (`algebraMap F E`) of the entry of the tensor at `numsAt σs v b`
    (Inst/Model/Common/TensorClaim.lean: `entryW`, which is `FFSeg.entryR`), if `InRows`; else 0.
  `live_iff`: the row part of an index is in range if and only if the index is, or the coordinate
    lies wholly in the column bits.
  `entry_cast`: the entry that is read from the image in a ring of an integer matrix is the image
    of the integer entry (`Layout.entry`, of which `Layout.weightsOf` is made).

Limits: this file does not say which families read which tensor with which variables. At an index
out of range in a coordinate that lies wholly in the column bits the atom reads entries of the
matrix at which no weight lies. More on this: the head of Cm/SegIdx.lean, Limits.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegIdx
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cm
open Cb Blocks Finset Inst.Model Inst.Model.Layout

/-- the list of sources is long enough for the coordinate, which is not empty, and has exactly
⌈log2 R⌉ bits if the kind is whole -/
def WidthOK (c : Coord) (σ : List Src) : Prop :=
  0 < c.R ∧ c.R ≤ 2 ^ σ.length ∧ (c.kind = .whole → σ.length = Nat.clog 2 c.R)

def WidthsOK : List Coord → List (List Src) → Prop
  | [], [] => True
  | c :: cs, σ :: σs => WidthOK c σ ∧ WidthsOK cs σs
  | _, _ => False

/-- the bits of every index, cut into the runs that the layout requires -/
def cutBits : List Coord → ℕ → List (List Src) → List CSrc
  | c :: cs, left, σ :: σs => CSrc.of c (tOf c left) σ :: cutBits cs (left - tOf c left) σs
  | _, _, _ => []

/-- The index atom of a weight tensor. -/
def tAtom {E : Type} [Field E] (P : Params) (k n : ℕ)
    (U : UnitS) (σs : List (List Src)) : IdxAtom E :=
  unitAtom P k n U (cutBits U.coords k σs)

/-- the index tuple that the vertex b encodes -/
def numsAt (σs : List (List Src)) (v b : ℕ) : List ℕ := σs.map fun σ => Src.num σ v b

/-- every index is inside its coordinate, but for the coordinates that lie wholly in the column
bits -/
def InRows : List Coord → ℕ → List ℕ → Prop
  | c :: cs, left, i :: is =>
    ((c.kind = .whole ∧ 0 < tOf c left) ∨ i < c.R) ∧ InRows cs (left - tOf c left) is
  | _, _, _ => True

namespace Spec

def t_ok : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (Φ : IdxFmt F) (v : ℕ) (P : Params)
      (n : ℕ) (U : UnitS) (σs : List (List Src)),
    WidthsOK U.coords σs → Src.OK σs.flatten v → (tAtom (E := E) P (Φ.hi + Φ.lo) n U σs).OK Φ v

open Classical in
def t_vtx : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (Φ : IdxFmt F) (v : ℕ) (P : Params)
      (n : ℕ) (U : UnitS) (σs : List (List Src)),
    WidthsOK U.coords σs → off (Φ.hi + Φ.lo) (units P) n + rows (Φ.hi + Φ.lo) U ≤ Φ.h →
    ∀ (W : ℕ → ℕ → F) (b : ℕ), (tAtom (E := E) P (Φ.hi + Φ.lo) n U σs).at Φ W (vtx v b) =
      if InRows U.coords (Φ.hi + Φ.lo) (numsAt σs v b) then
        algebraMap F E (entryW P (Φ.hi + Φ.lo) W n U (numsAt σs v b))
      else 0

def live_iff : Prop :=
  ∀ (c : Coord) (left i : ℕ),
    (split c (tOf c left) i).2 < lOf c (tOf c left) ↔ ((c.kind = .whole ∧ 0 < tOf c left) ∨ i < c.R)

def entry_cast : Prop :=
  ∀ (R : Type) [CommRing R] (P : Params) (k : ℕ) (M : Mat) (n : ℕ) (U : UnitS) (i : List ℕ),
    entryW P k (fun y c => ((M y c : ℤ) : R)) n U i = ((entry k (units P) M n U i : ℤ) : R)

end Spec
end Cm
