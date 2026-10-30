-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdx.lean: index atoms from bits. A generic way to write down an index atom (`IdxAtom` with
its law `IdxAtom.OK`, Cb/Req/ReqSpec.lean: a vector on the vertices of a cube, linear in the index
matrix, whose multilinear extension at every point is a tensor form), and the atoms of the units of
the model's layout.

Definitions and statements; proofs: Cm/SegIdxProofs.lean, Cm/SegIdxUnitProofs.lean.

Part of the arithmetisation of the model. The cells must meet zero tests (identities) and table
lookups (keys) at the vertices of Boolean cubes (`SegSpec.Holds`, Cb/Req/ReqSpec.lean). The
conditions read the model's weights off one matrix, the index matrix, through index atoms. Used in
Cm/SegIdxTensor.lean and Cm/TargetSegIdxModel.lean.

 1. `Src`: where a bit comes from: a variable of the cube, the negation of a variable (an index
    with its lowest bit flipped: the partner in a rotation), or a constant. (The rotation of
    Cm/TargetSegFFMat.lean, `wpart` at `.QK`, takes constants, `.bit`, not `.nvar`.) A list of
    sources is at a vertex a number (`Src.num`) and at a point a point (`Src.pt`).
 2. `ofBits cs rs T`: the generic constructor. cs: the sources of the bits of the column number (as
    many as the matrix has column bits). rs: the sources of some further bits, the row bits; T r y:
    the coefficient of row y when the row bits form the number r (any public table).
        column point ψ(pt) = the point of cs;
        row factor g(pt)[y] = ∑_r eq(the point of rs, r) · T r y.
    At a vertex b it reads ∑_y T (number of rs at b) y · W[y][number of cs at b]
    (`Spec.ofBits_vtx`). If no variable is named twice in cs and rs together, and all are below the
    cube's number v of variables, it has the law of an index atom (`Spec.ofBits_ok`). Variables of
    the cube that no source names are not read: the vector is constant in them.
 3. Units of the layout (Inst/Model/Layout.lean: a weight tensor W[i_1, .., i_n]; every coordinate
    i_g splits into a column part and a row part; digits in base 256 in different rows).
    `CSrc`: the sources of the bits of one coordinate, in three runs A, B, C: the index is the
    number of A ++ B ++ C, its column part the number of B, its row part the number of A ++ C, if
    the runs fit (`CSrc.Fits`).
    `unitAtom`: the atom of the unit number n: the table T puts 256^j at the row of digit j, and
    nothing where a row part is out of range.

Main names (stated in `Spec`, each under the hypotheses of its statement): `ofBits_ok`,
`ofBits_vtx`; `unit_ok`; `unit_vtx`: at a vertex the atom is the image in E (`algebraMap F E`) of
the entry of the tensor that the layout reads from the matrix (`entryW`,
Inst/Model/Common/TensorClaim.lean) at the indices that the vertex encodes, if all row parts are in
range, and 0 if not. `live_of_inUnit`, `of_fits`: see their doc comments.

Limits: there are dead vertices at which an atom is not 0 (as a function of the index matrix). In
this file a vertex is called dead if the indices that it encodes are not inside the unit (`InUnit`,
Inst/Model/Layout.lean: each index below the size of its coordinate); this is not the negation of
`LiveAt`, which speaks of row parts alone. A coordinate of kind whole that lies wholly in the
column bits has no row part. The vocabulary is such a coordinate: 202,048 of 2^18 columns. At a
vertex whose index there is out of range the atom reads the matrix at a column in which no weight
lies in this unit's rows: the value is whatever the index matrix holds there. Such entries are free
within the ranges of an index. A tensor form cannot do otherwise: eq(ψ, ·) does not vanish on those
columns. So a family that uses such an atom must have a coefficient table that is 0 at those
vertices.
This file says nothing on cells, segments or protocols. It does not say which tensors the model's
conditions read, with which variables: Cm/TargetSegIdxModel.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqSpec
import Inst.Model.Common.TensorClaim
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cm
open Cb Blocks Finset Inst.Model Inst.Model.Layout

/-! ## 1. Sources of bits -/

/-- Where a bit comes from. -/
inductive Src where
  | var (u : ℕ)
  /-- the negation of a variable -/
  | nvar (u : ℕ)
  | bit (β : Bool)

namespace Src

/-- the coordinate that the source names, at a point; for a negation 1 minus it; for a constant 0
or 1 -/
def eval {E : Type} [Zero E] [One E] [Sub E] (s : Src) (pt : ℕ → E) : E :=
  match s with
  | .var u => pt u
  | .nvar u => 1 - pt u
  | .bit β => if β then 1 else 0

/-- the bit at the vertex b of a cube of v variables (variable 0 = most significant bit of b) -/
def bitAt (s : Src) (v b : ℕ) : Bool :=
  match s with
  | .var u => decide (u < v) && b.testBit (v - 1 - u)
  | .nvar u => !(decide (u < v) && b.testBit (v - 1 - u))
  | .bit β => β

/-- the variables that a list of sources names -/
def vars : List Src → List ℕ
  | [] => []
  | .var u :: l => u :: vars l
  | .nvar u :: l => u :: vars l
  | .bit _ :: l => vars l

/-- every variable is below v, none is named twice -/
def OK (l : List Src) (v : ℕ) : Prop := (vars l).Nodup ∧ ∀ u ∈ vars l, u < v

/-- a list of sources as a point; 0 beyond its length -/
def pt {E : Type} [Zero E] [One E] [Sub E] : List Src → (ℕ → E) → ℕ → E
  | [], _, _ => 0
  | s :: _, q, 0 => s.eval q
  | _ :: l, q, t + 1 => pt l q t

end Src

/-- the number of a list of bits, most significant first -/
def numL : List Bool → ℕ
  | [] => 0
  | β :: l => (if β then 2 ^ l.length else 0) + numL l

/-- the number that a list of sources forms at the vertex b -/
def Src.num (l : List Src) (v b : ℕ) : ℕ := numL (l.map fun s => s.bitAt v b)

/-! ## 2. The generic constructor -/

/-- An index atom from the sources of its column bits, the sources of its row bits, and a table of
row factors. -/
def ofBits {E : Type} [Field E] (cs rs : List Src) (T : ℕ → ℕ → E) : IdxAtom E where
  g := fun q y => ∑ r ∈ range (2 ^ rs.length), eqN rs.length 0 (Src.pt rs q) r * T r y
  ψ := fun q => Src.pt cs q

/-! ## 3. The units of the layout -/

/-- The sources of the bits of one coordinate, in three runs. -/
structure CSrc where
  A : List Src
  B : List Src
  C : List Src

namespace CSrc
/-- all bits of the index, most significant first -/
def all (x : CSrc) : List Src := x.A ++ x.B ++ x.C
/-- the bits of the row part -/
def rowBits (x : CSrc) : List Src := x.A ++ x.C

/-- the runs have the lengths that the kind of the coordinate requires, when it takes t column
bits -/
def Fits (x : CSrc) (c : Coord) (t : ℕ) : Prop :=
  x.B.length = t ∧
  match c.kind with
  | .low => x.C = []
  | .high => t ≤ sOf c.R ∧ x.C.length = sOf c.R - t
  | .whole => x.C = [] ∧ (0 < t → x.A = [])

/-- from all bits σ of an index: the runs for a coordinate that takes t column bits -/
def of (c : Coord) (t : ℕ) (σ : List Src) : CSrc :=
  match c.kind with
  | .low => ⟨σ.take (σ.length - t), σ.drop (σ.length - t), []⟩
  | .high =>
    ⟨σ.take (σ.length - sOf c.R),
      (σ.drop (σ.length - sOf c.R)).take t,
      (σ.drop (σ.length - sOf c.R)).drop t⟩
  | .whole => if 0 < t then ⟨[], σ, []⟩ else ⟨σ, [], []⟩
end CSrc

/-- every coordinate's runs fit; "left" is the counter of column bits of the layout -/
def FitsAll : List Coord → ℕ → List CSrc → Prop
  | [], _, [] => True
  | c :: cs, left, x :: xs => x.Fits c (tOf c left) ∧ FitsAll cs (left - tOf c left) xs
  | _, _, _ => False

/-- the column bits of a unit: the first coordinate has the lowest bits -/
def colSrc : List CSrc → List Src
  | [] => []
  | x :: xs => colSrc xs ++ x.B
/-- its row bits, in the same order -/
def rowSrc : List CSrc → List Src
  | [] => []
  | x :: xs => rowSrc xs ++ x.rowBits

/-- the index tuple that the vertex b encodes -/
def idxAt (xs : List CSrc) (v b : ℕ) : List ℕ := xs.map fun x => Src.num x.all v b

/-- the row inside the unit, from the digit j and the number r of the row bits -/
def rowDec (j : ℕ) : List Coord → ℕ → List CSrc → ℕ → ℕ
  | c :: cs, left, x :: xs, r =>
    r % 2 ^ x.rowBits.length +
      lOf c (tOf c left) * rowDec j cs (left - tOf c left) xs (r / 2 ^ x.rowBits.length)
  | _, _, _, _ => j

/-- all row parts are in range -/
def rowLive : List Coord → ℕ → List CSrc → ℕ → Prop
  | c :: cs, left, x :: xs, r =>
    r % 2 ^ x.rowBits.length < lOf c (tOf c left) ∧
    rowLive cs (left - tOf c left) xs (r / 2 ^ x.rowBits.length)
  | _, _, _, _ => True

/-- the same on an index tuple -/
def LiveAt : List Coord → ℕ → List ℕ → Prop
  | c :: cs, left, i :: is =>
    (split c (tOf c left) i).2 < lOf c (tOf c left) ∧ LiveAt cs (left - tOf c left) is
  | _, _, _ => True

open Classical in
/-- the table of row factors of a unit whose first row is o: 256^j at the row of digit j -/
def unitTab {E : Type} [Field E] (k o : ℕ) (U : UnitS) (xs : List CSrc) :
    ℕ → ℕ → E := fun r y =>
  if rowLive U.coords k xs r then
    ∑ j ∈ range U.nU, if y = o + rowDec j U.coords k xs r then (256 : E) ^ j
  else 0 else 0

/-- The index atom of the unit U with the number n, its coordinates read from the sources xs. -/
def unitAtom {E : Type} [Field E] (P : Params) (k n : ℕ)
    (U : UnitS) (xs : List CSrc) : IdxAtom E :=
  ofBits (List.replicate (k - (colSrc xs).length) (.bit false) ++ colSrc xs)
    (rowSrc xs) (unitTab k (off k (units P) n) U xs)

/-- all sources of a unit's coordinates -/
def allSrc (xs : List CSrc) : List Src := colSrc xs ++ rowSrc xs

/-! ## The statements -/

namespace Spec

/-- States: under the hypotheses below, the generic constructor gives an index atom. -/
def ofBits_ok : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (Φ : IdxFmt F) (v : ℕ)
      (cs rs : List Src) (T : ℕ → ℕ → E),
    cs.length = Φ.hi + Φ.lo → Src.OK (cs ++ rs) v → (ofBits cs rs T).OK Φ v

/-- States what the generic constructor's atom reads at a vertex. -/
def ofBits_vtx : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (Φ : IdxFmt F) (v : ℕ)
      (cs rs : List Src) (T : ℕ → ℕ → E),
    cs.length = Φ.hi + Φ.lo →
    ∀ (W : ℕ → ℕ → F) (b : ℕ), (ofBits cs rs T).at Φ W (vtx v b) =
      ∑ y ∈ range Φ.h, T (Src.num rs v b) y * algebraMap F E (W y (Src.num cs v b))

/-- States: under the hypotheses below, the atom of a unit has the law of an index atom. -/
def unit_ok : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (Φ : IdxFmt F) (v : ℕ) (P : Params)
      (n : ℕ) (U : UnitS) (xs : List CSrc),
    FitsAll U.coords (Φ.hi + Φ.lo) xs → Src.OK (allSrc xs) v →
    (unitAtom (E := E) P (Φ.hi + Φ.lo) n U xs).OK Φ v

open Classical in
/-- States: under the hypotheses below, at a vertex the atom of a unit is the image in E of the
entry of the tensor, or 0 where a row part is out of range. -/
def unit_vtx : Prop :=
  ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (Φ : IdxFmt F) (v : ℕ) (P : Params)
      (n : ℕ) (U : UnitS) (xs : List CSrc),
    FitsAll U.coords (Φ.hi + Φ.lo) xs → off (Φ.hi + Φ.lo) (units P) n + rows (Φ.hi + Φ.lo) U ≤ Φ.h →
    ∀ (W : ℕ → ℕ → F) (b : ℕ), (unitAtom (E := E) P (Φ.hi + Φ.lo) n U xs).at Φ W (vtx v b) =
      if LiveAt U.coords (Φ.hi + Φ.lo) (idxAt xs v b) then
        algebraMap F E (entryW P (Φ.hi + Φ.lo) W n U (idxAt xs v b))
      else 0

/-- States: indices inside the unit have their row parts in range. -/
def live_of_inUnit : Prop :=
  ∀ (cs : List Coord) (left : ℕ) (is : List ℕ), InUnit cs is → LiveAt cs left is

/-- States: under the hypotheses below, the runs that `CSrc.of` cuts fit, and together they are the
bits given. -/
def of_fits : Prop :=
  ∀ (c : Coord) (t : ℕ) (σ : List Src), (c.kind = .low → t ≤ σ.length) →
    (c.kind = .high → t ≤ sOf c.R ∧ sOf c.R ≤ σ.length) → (c.kind = .whole → 0 < t → σ.length = t) →
    (CSrc.of c t σ).Fits c t ∧ (CSrc.of c t σ).all = σ

end Spec
end Cm
