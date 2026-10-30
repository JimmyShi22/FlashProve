-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBits.lean: separable atoms: a cell atom whose rows are read off one set of variables
and whose columns off another has a reading with at most one item a piece; and a calculus to derive
"separable, with at most n pieces" family by family.

A cell atom is a function on the vertices b < 2^v of a cube whose values are affine forms in the
cells (`CForm`, Cb/Req/ReqSpec.lean). A reading of it (`LdPartRg.Of`, Cb/Part/LdPartRead.lean)
gives, for all matrices A of cells and every point γ, the multilinear extension of its values as a
constant plus items, each weights on rows times weights on columns of one segment's matrix, all
functions of γ.

Definitions and statements (each a `Prop` in `Cm.TR.Spec`); the proofs are in
Cm/TargetReadBitsProofs.lean. Generic: any field; nothing here knows a model or a protocol.



Why: every atom whose places lie in the first n segments and in the shapes R, C (the numbers of rows
and columns of each segment's matrix) has the reading by columns (`ldPartByCol`,
Cb/Part/LdPartRead.lean). That reading has one item for each column of each matrix at hand, and each
item costs a read: a whole row of entries. At a real model, whose matrices have thousands of
columns, the reads' message is then by far the largest message of a body, and some thousand times
larger than with one item a piece. Cm/TargetRead.lean states that an atom given by bits, with
`BitAtom.OK`, has a reading (there `Reading.Of`: the same notion under another name) with one item a
piece (`Spec.read_bits`). The model's places are a little wider than its pieces. Rows are numbered
by bits, but columns by a function of bits that is no bit pattern: an offset, and division by a
width that is no power of two, whose quotient moves the block of rows. And some atoms read the row
before.

Main names:
  `SPiece`: a segment; two lists cs, rs of sources of bits (`Src`, Cm/SegIdx.lean); tables α (number
    of cs, row), β (number of rs, column). At the vertex b the piece is Σ_{r, y} α (number of cs at
    b) r · β (number of rs at b) y · A seg r y (r, y in the shapes R, C).
  `sepItem P`: its item (`LdPartItem`, Cb/Part/LdPartRead.lean). Rank one: one read.
  `SepAtom`, `SepAtom.OK`: constants at the vertices and a list of pieces; in every piece no
    variable is named twice in cs and rs together, and all are below v.
  `SepV R C v n F`: the predicate, on value functions F b A: there is a `SepAtom` with OK and at
    most n pieces whose value at every vertex b < 2^v and all matrices A is F b A. `Sep R C v n f`:
    the same of an atom f.
  `Spec.sep_read`: Sep R C v n f ⇒ f has a reading in the shapes R, C with at most n items.
  `Spec.sep_bits`: Cm/TargetRead.lean's atoms given by bits, with `BitAtom.OK`, are separable, a
    piece for a piece.
The calculus:
  `Spec.sep_congr`, `Spec.sep_mono`: the predicate reads F at the vertices b < 2^v alone; more
    pieces are allowed.
  `Spec.sep_const`: F b A := k b: no piece.
  `Spec.sep_add`, `Spec.sep_smul`, `Spec.sep_sub`, `Spec.sep_sum`: sums (n + m), multiples by a
    constant (n), differences (n + m), Σ_{k < m} (m · n).
  `Spec.sep_cell`, the base: cs, rs with Src.OK (cs ++ rs) v; a guard gT on the number t of cs, a
    guard gU on the number u of rs; a coefficient c u; a block number q u; a row ρ t (q u); a column
    κ u. F b A := if gT t ∧ gU u then c u · A seg (ρ t (q u)) (κ u) else 0 is separable with at most
    Q pieces, if, at the numbers t < 2^|cs|, u < 2^|rs|, q u < Q under gU u and under the guards the
    place lies in the shapes.
An instance that meets the hypotheses of `Spec.sep_cell` and of `Spec.sep_read`: `sep_guard`,
Cm/TargetReadBitsProofs.lean.

A remark (by inspection). A guard or a coefficient that reads a variable outside the
row's and the column's variables (say bits that select a layer or an instance) is taken in by
putting that variable into rs (or cs) as an idle source, which κ (or ρ) ignores: α and β are
arbitrary tables. Of a coefficient this file's rule bears it for rs alone (the c of `Spec.sep_cell`
reads the number of rs); for cs the definition does (`SPiece.α`).


How this stands to this protocol's technical report (lean/CREDITS.md; the same inspection): towards,
and wider. There a cell map belongs to one matrix; some of its variables are the matrix's row bits,
others its column bits:
two disjoint selections; its value is a public constant plus a sum over the matrix's parts of (a
public integer) · (the cell at (row bits, part), column bits). One piece renders one part; "one item
a piece, rank one" is the report's count: one read row for each part. Any tables, guards, a
shift by one position, columns by division with remainder, a block number read off the column's
variables: wider; they cost pieces (of these the block number alone enters the bound of
`Spec.sep_cell`: Q). A variable in both row and column is excluded there too. Sharing there: a pair
(matrix, row point) stands once in the list of reads and serves every map on that matrix at that row
point: here: pieces with the same segment, cs and α at the same point of cs: among the maps of one
sumcheck.

Limits: this file does not say that a model's atoms are separable. It does not say that reads are
shared: pieces with the same segment, cs and α have the same row weights and could be served by one
read. A place whose row and column read the same variable is not taken in. It says nothing on
protocols, errors or cost.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetRead
import Cb.Part.LdPartRead

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset

variable {E : Type} [Field E]

/-- A separable piece. -/
structure SPiece (E : Type) where
  seg : ℕ
  cs : List Src
  rs : List Src
  α : ℕ → ℕ → E
  β : ℕ → ℕ → E

/-- The piece at a vertex. -/
def SPiece.at (P : SPiece E) (R C : ℕ → ℕ) (v b : ℕ) (A : ℕ → ℕ → ℕ → E) : E :=
  ∑ r ∈ range (R P.seg),
    ∑ y ∈ range (C P.seg), P.α (Src.num P.cs v b) r * P.β (Src.num P.rs v b) y * A P.seg r y

/-- Its item. -/
def sepItem (P : SPiece E) : LdPartItem E where
  seg := P.seg
  row := fun γ r => ∑ t ∈ range (2 ^ P.cs.length), eqN P.cs.length 0 (Src.pt P.cs γ) t * P.α t r
  col := fun γ y => ∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.β u y

/-- A separable atom. -/
structure SepAtom (E : Type) where
  k : ℕ → E
  pieces : List (SPiece E)

def SepAtom.OK (B : SepAtom E) (v : ℕ) : Prop := ∀ P ∈ B.pieces, Src.OK (P.cs ++ P.rs) v

/-- Its value at a vertex. -/
def SepAtom.at (B : SepAtom E) (R C : ℕ → ℕ) (v b : ℕ) (A : ℕ → ℕ → ℕ → E) : E :=
  B.k b + (B.pieces.map fun P => P.at R C v b A).sum

/-- Its reading: one item a piece. -/
def SepAtom.reading (B : SepAtom E) (v : ℕ) : LdPartRg E :=
  ⟨fun γ => ext v B.k γ, B.pieces.map sepItem⟩

/-- Separable, with at most n pieces: on value functions. -/
def SepV (R C : ℕ → ℕ) (v n : ℕ) (F : ℕ → (ℕ → ℕ → ℕ → E) → E) : Prop :=
  ∃ B : SepAtom E, (∀ b < 2 ^ v, ∀ A, F b A = B.at R C v b A) ∧ B.OK v ∧ B.pieces.length ≤ n

/-- The same of an atom. -/
def Sep (R C : ℕ → ℕ) (v n : ℕ) (f : ℕ → CForm E) : Prop := SepV R C v n fun b A => (f b).val A

/-- the source, in a cube with d more variables in front -/
def _root_.Cm.Src.up (d : ℕ) : Src → Src
  | .var u => .var (d + u)
  | .nvar u => .nvar (d + u)
  | .bit β => .bit β

namespace Spec

/-- States: an atom that is separable with at most n pieces has a reading with at most n items. -/
def sep_read : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n : ℕ) (f : ℕ → CForm E),
    Sep R C v n f → ∃ ρ : LdPartRg E, ρ.Of R C v f ∧ ρ.items.length ≤ n

/-- States: an atom given by bits (`B.Is C v f`) with `B.OK R v` is separable. -/
def sep_bits : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E) (B : BitAtom E),
    B.Is C v f → B.OK R v → Sep R C v B.pieces.length f

def sep_congr : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n : ℕ) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    (∀ b < 2 ^ v, ∀ A, F b A = G b A) → SepV R C v n G → SepV R C v n F

def sep_mono : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n m : ℕ) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    n ≤ m → SepV R C v n F → SepV R C v m F

def sep_const : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (k : ℕ → E), SepV R C v 0 fun b _ => k b

def sep_add : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n m : ℕ) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepV R C v n F → SepV R C v m G → SepV R C v (n + m) fun b A => F b A + G b A

def sep_smul : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n : ℕ) (c : E) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepV R C v n F → SepV R C v n fun b A => c * F b A

def sep_sub : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n m : ℕ) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepV R C v n F → SepV R C v m G → SepV R C v (n + m) fun b A => F b A - G b A

def sep_sum : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v n m : ℕ) (F : ℕ → ℕ → (ℕ → ℕ → ℕ → E) → E),
    (∀ k < m, SepV R C v n (F k)) → SepV R C v (m * n) fun b A => ∑ k ∈ range m, F k b A

/-- The base: one cell. -/
def sep_cell : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg Q : ℕ) (cs rs : List Src) (gT gU : ℕ → Prop)
      [DecidablePred gT] [DecidablePred gU] (c : ℕ → E) (q : ℕ → ℕ) (ρ : ℕ → ℕ → ℕ) (κ : ℕ → ℕ),
    Src.OK (cs ++ rs) v → (∀ u < 2 ^ rs.length, gU u → q u < Q) →
    (∀ t < 2 ^ cs.length, ∀ u < 2 ^ rs.length, gT t → gU u → ρ t (q u) < R seg ∧ κ u < C seg) →
    SepV R C v Q fun b A =>
      if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        c (Src.num rs v b) * A seg (ρ (Src.num cs v b) (q (Src.num rs v b))) (κ (Src.num rs v b))
      else 0

/-- More variables in front. -/
def sep_low : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v d n : ℕ) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepV R C v n F → SepV R C (d + v) n fun b A => F (b % 2 ^ v) A

end Spec

end Cm.TR
