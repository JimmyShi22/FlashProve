-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetRead.lean: a claim on a cell atom at a point, as weights on rows times weights on columns:
readings.

A cell atom is a function on the vertices b < 2^v of a cube whose values are affine forms in the
cells (`CForm`, Cb/Req/ReqSpec.lean). A reading writes its multilinear extension, at every point γ
and for all matrices A of cells, as a term free of A plus a list of terms Σ_{r < R seg, c < C seg}
row r · col c · A seg r c, whose vectors row, col depend on γ alone (R, C, the shapes: the numbers
of rows and columns of each segment's matrix).

Definitions and statements (`Cm.TR.Spec.read_byCol`, `Cm.TR.Spec.read_bits`); the proofs are in
Cm/TargetReadProofs.lean. Generic: any field; nothing here knows a model or a protocol. `BitAtom` is
what `Spec.sep_bits` (Cm/TargetReadBits.lean) speaks of; items and readings are there those of
Cb/Part/LdPartRead.lean (`LdPartItem`, `LdPartRg`, `LdPartRg.Of`; its reading by columns:
`ldPartByCol`): the same notions under other names.

Why: a sumcheck on a family (Cb/Req/ReqSpec.lean) leaves, for each atom that is affine in cells, the
claim "the multilinear extension of the atom's values, at the point γ, is v". The
read stage (Cb/Ld/LdRead.lean: `ReadCl`, `readsOf`) takes claims of one form: constant + Σ_k Σ_c cw
k c · (Σ_r W k r · Y r c) + masks = target: reads (a vector W k of weights on the rows of the matrix
of cells, applied to all columns) and coefficients on the entries of the reads. By its Lean type a
cell atom is, at each vertex, an arbitrary affine form (`CForm`); a write-up of ours
(lean/CREDITS.md) has a fixed public combination over the parts of one matrix, with row bits and
column bits among the variables,
so that a claim at a point is a partial evaluation: one read. Here: what a reading is; that every
atom whose places lie in the shapes has one (a large one); that an atom given by bits, with
`B.OK R v`, has a small one.

Main names:
  `Item`, `Item.val`: an item, one of a reading's terms, and its value; `Reading`: its term free of
    A and its list of items (their fields: see the records); `ρ.Of R C v f`: ρ is a reading of f.
  `byCol n C v f`, the reading by columns: one item for each (segment s < n, column c < C s).
  `Piece`: a piece given by bits (`Src`, Cm/SegIdx.lean): a segment s, a first row R0, sources cs of
    the bits of the row number inside a block of 2^|cs| rows, sources rs of further bits, a table T
    u y: at the vertex b the piece is Σ_{y < C s} T (number of rs at b) y · A s (R0 + number of cs
    at b) y. Its item: `bitItem`.
  `BitAtom`, `B.Is C v f`: constants at the vertices and a list of pieces; "f is B": at every vertex
    b < 2^v and all A the form's value is the constant plus the pieces.
  `B.OK R v`: in every piece no variable is named twice in cs and rs together, all are below v, and
    the block of rows lies in the segment's matrix.
  `Spec.read_byCol`: every atom all of whose places, at the vertices, lie in the first n segments
    and in the shapes has the reading byCol. So a builder of a request has, for every partition
    whose segments read inside the shapes,
    a list of reads for each cell atom; its length is the number of columns of
    the n matrices together.
  `Spec.read_bits`: an atom that is a BitAtom with OK has the reading with one item a piece.

How this stands to the write-up (by two inspections): towards, and wider. There a cell map
stands on one matrix, whose rows are numbered by (all its row bits, a part) and whose columns by all
its column bits: constant + Σ_parts (a public integer) · cell; at a point (z, ζ) it is constant +
Σ_parts (that integer) · Σ_columns eq(ζ, column) · (the read of that part at z). A piece renders one
part: R0 the first row of the part, cs the row bits, rs the column bits, T u y := the integer if y =
(the matrix's first column) + u, else 0. A general table T is wider than that; byCol has no
counterpart there. Variables of the cube that neither cs nor rs names are allowed (a map takes only
some of the variables): the extension sums them out.

Limits: this file does not say that the model's atoms are BitAtoms.
It does not say that reads are shared: in the write-up a pair (matrix, row point) stands
once in the list of reads and serves all parts, all maps and all column points; here each piece has
an item of its own; "items with the same segment, first row and sources cs are one read" is owed to
whoever counts.
It says nothing on whose matrices are read: items name this or an earlier segment alike. In the
write-up reads are sent for earlier matrices too, and the reading segment's range check
covers them again.
This file says nothing on protocols, errors or cost.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cm.SegIdx
import Cm.SegAlg

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset

variable {E : Type} [Field E]

/-- One item of a reading. -/
structure Item (E : Type) where
  seg : ℕ
  row : (ℕ → E) → ℕ → E
  col : (ℕ → E) → ℕ → E

/-- Its value at the matrices A, in the shapes R (rows), C (columns). -/
def Item.val (t : Item E) (R C : ℕ → ℕ) (γ : ℕ → E) (A : ℕ → ℕ → ℕ → E) : E :=
  ∑ r ∈ range (R t.seg), ∑ c ∈ range (C t.seg), t.row γ r * t.col γ c * A t.seg r c

/-- A reading. -/
structure Reading (E : Type) where
  k0 : (ℕ → E) → E
  items : List (Item E)

/-- ρ is a reading of the atom f on v variables. -/
def Reading.Of (ρ : Reading E) (R C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E) : Prop :=
  ∀ (A : ℕ → ℕ → ℕ → E) (γ : ℕ → E),
    ext v (fun b => (f b).val A) γ = ρ.k0 γ + (ρ.items.map fun t => t.val R C γ A).sum

/-- The coefficient of an affine form at a place. -/
def coefAt (g : CForm E) (q : Cb.Place) : E := (g.terms.map fun t => if t.2 = q then t.1 else 0).sum

/-- The reading by columns: one item for each column. That it is a reading: `Spec.read_byCol`, under
its premise. -/
def byCol (n : ℕ) (C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E) : Reading E where
  k0 := fun γ => ext v (fun b => (f b).c0) γ
  items := (List.range n).flatMap fun s => (List.range (C s)).map fun c =>
    ⟨s, fun γ r => ext v (fun b => coefAt (f b) (s, r, c)) γ, fun _ c' => if c' = c then 1 else 0⟩

/-- A piece given by bits. -/
structure Piece (E : Type) where
  seg : ℕ
  R0 : ℕ
  cs : List Src
  rs : List Src
  T : ℕ → ℕ → E

/-- The piece at a vertex. -/
def Piece.at (P : Piece E) (C : ℕ → ℕ) (v b : ℕ) (A : ℕ → ℕ → ℕ → E) : E :=
  ∑ y ∈ range (C P.seg), P.T (Src.num P.rs v b) y * A P.seg (P.R0 + Src.num P.cs v b) y

/-- The item of a piece given by bits. -/
def bitItem (P : Piece E) : Item E where
  seg := P.seg
  row := fun γ r =>
    if P.R0 ≤ r ∧ r < P.R0 + 2 ^ P.cs.length then eqN P.cs.length 0 (Src.pt P.cs γ) (r - P.R0)
    else 0
  col := fun γ y => ∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.T u y

/-- An atom given by bits. -/
structure BitAtom (E : Type) where
  k : ℕ → E
  pieces : List (Piece E)

/-- f is the atom B. -/
def BitAtom.Is (B : BitAtom E) (C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E) : Prop :=
  ∀ b < 2 ^ v, ∀ A : ℕ → ℕ → ℕ → E, (f b).val A = B.k b + (B.pieces.map fun P => P.at C v b A).sum

def BitAtom.OK (B : BitAtom E) (R : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ P ∈ B.pieces, Src.OK (P.cs ++ P.rs) v ∧ P.R0 + 2 ^ P.cs.length ≤ R P.seg

/-- The reading of an atom given by bits: one item a piece. -/
def BitAtom.reading (B : BitAtom E) (v : ℕ) : Reading E :=
  ⟨fun γ => ext v B.k γ, B.pieces.map bitItem⟩

namespace Spec

/-- States: every atom all of whose places, at the vertices, lie in the first n segments and in the
shapes has a reading: `byCol`. -/
def read_byCol : Prop :=
  ∀ (E : Type) [Field E] (n : ℕ) (R C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E),
    (∀ b < 2 ^ v, ∀ t ∈ (f b).terms, t.2.1 < n ∧ t.2.2.1 < R t.2.1 ∧ t.2.2.2 < C t.2.1) →
    (byCol n C v f).Of R C v f

/-- States: an atom given by bits (`B.Is C v f`) with `B.OK R v` has a reading with one item a
piece. -/
def read_bits : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E) (B : BitAtom E),
    B.Is C v f → B.OK R v → (B.reading v).Of R C v f

end Spec

end Cm.TR
