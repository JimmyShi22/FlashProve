-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSpec.lean: the conditions of a request, cut into segments: the data and its laws.

This file defines the form in which the constraint system of the indexed relation is written for the
sub-protocol that reduces it: polynomial identities and lookup conditions, at the vertices of
Boolean cubes, in cells and in the index matrix, and bounds on the cells; cut into pieces, the
segments.
Definitions only, and the statements of two small laws (in `Cb.Spec`; the proofs are in
Cb/Req/ReqSpecProofs.lean). No protocol.

The preamble of a request treats the conditions of the model one segment at a time.






Main names:
  `Fam`: a family of conditions: a sum of terms over atoms of three kinds, on the vertices b < 2^v.
  `SegSpec`: a segment: the shape of its matrix of cells, its families of identities, its families
    of keys with their tables (`Tab`).








How it renders the print's notion of a partition into segments. There: one polynomial
map and key maps for each segment (also in the revised edition, whose section on constraint
relations defines "vanishes on the cube" for a tuple of maps too, without the section on a request
using it), polynomials with public coefficients in the multilinear extensions of vector maps of
three forms. Here the same three forms (`Atom0.cell`, `Atom0.idx`, `Atom.sum`), in a normal form:
sums of terms.
The predicates "vanishes on the cube" and "every key on the cube lies in its table" read a
polynomial map at vertices only, where an extension is the vector itself. So conditions are given by
their values at vertices; the polynomial behind a family (extensions of the coefficient tables and
of the atoms) is formed where a sumcheck needs it, with a degree that is computed from the lists.
Dead vertices (an index set is rarely a power of two) need no notion: a coefficient table is 0 there
(identities), or a term without atoms puts an element of the table there (keys).

Limits: declared differences. (1) Several families in place of one polynomial map (here a list of
families, each with its own number of variables; Cb/Req/ReqGlue.lean joins them into ONE family by
further variables, which is the paper's one map; Cb/Req/ReqFamTuple.lean combines them on one cube
with a drawn coefficient for each, which the paper's section on a request does not do). (2) "admit"
and "force" are implications, not the paper's one equivalence; they are what completeness and
knowledge soundness use. "force" holds the remark that the conditions read a message of the encoded
index only through the matrix "mat", and that the index which the message holds is the one for which
the witness is valid. (3) A public test "pub" of the instance (the form of a request) stands beside
the conditions. (The revised edition has a test of the form too; the model's pub has one clause
more, which there is a condition of the model.) (4) That the verifier can evaluate the extensions of
the public coefficients fast is not rendered: Lean models no running time.
This file says nothing on any protocol, code or oracle.


The notions follow definitions of this protocol's technical report (lean/CREDITS.md).

Terms: lean/GLOSSARY.md: atom, cell, conditions (of a segment), configuration, encoded index,
family, index matrix, key, place, preamble, segment, table, tensor form, term.
"The print": a print of this protocol's technical report (lean/CREDITS.md); it is
not in this repository.
-/
import Cb.Gen.Tensor
import Blocks.Ext

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

/-- A place in the matrices of cells: (segment, row, column). -/
abbrev Place : Type := ℕ × ℕ × ℕ

/-- The 0/1 point of the v-bit number b; the first coordinate belongs to the most significant bit,
as in Blocks/Basic.lean; 0 beyond the v coordinates. -/
def vtx {E : Type} [Zero E] [One E] (v b : ℕ) : ℕ → E := fun t =>
  if t < v ∧ b.testBit (v - 1 - t) then 1 else 0

/-- An affine form in cells: a constant and finitely many (coefficient, place). -/
structure CForm (E : Type) where
  c0 : E
  terms : List (E × Place)

/-- An index atom: the data. From a point: the row factor and the column point of a tensor form. -/
structure IdxAtom (E : Type) where
  g : (ℕ → E) → ℕ → E
  ψ : (ℕ → E) → ℕ → E

/-- An atom of the first two kinds: at the vertex b an affine form in cells; or an index atom. -/
inductive Atom0 (E : Type) where
  | cell (f : ℕ → CForm E)
  | idx (a : IdxAtom E)

/-- A term: a table of public coefficients (instance, vertex) and the numbers of the atoms whose
product it multiplies. -/
structure Term (X E : Type) where
  coef : X → ℕ → E
  atoms : List ℕ

/-- A sum of terms over na numbered atoms of the first two kinds, on v variables. -/
structure Poly0 (X E : Type) where
  v : ℕ
  na : ℕ
  atom : ℕ → Atom0 E
  terms : List (Term X E)

/-- An atom: of the first two kinds, or the sum over w further variables of a sum of terms (a matrix
product, a sum over positions). -/
inductive Atom (X E : Type) where
  | base (a : Atom0 E)
  | sum (w : ℕ) (P : Poly0 X E)

/-- A family of conditions: the data. One value at each vertex b < 2^v. -/
structure Fam (X E : Type) where
  v : ℕ
  na : ℕ
  atom : ℕ → Atom X E
  terms : List (Term X E)

/-- A table: the values of t on the numbers below 2^T (repeats allowed). -/
structure Tab (F : Type) where
  T : ℕ
  t : ℕ → F

/-- A segment: the data. Its matrix of cells has 2^rowsLog rows and cols columns. -/
structure SegSpec (X F E : Type) where
  rowsLog : ℕ
  cols : ℕ
  idn : List (Fam X E)
  keys : List (Fam X E × Tab F)

/-! ## Values at vertices -/

section Val
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- The value of an affine form at the matrices A (entries read in E). -/
def CForm.val (f : CForm E) (A : ℕ → ℕ → ℕ → E) : E :=
  f.c0 + (f.terms.map fun t => t.1 * A t.2.1 t.2.2.1 t.2.2.2).sum

/-- The tensor form of an index atom at a point. -/
def IdxAtom.at (a : IdxAtom E) (Φ : IdxFmt F) (W : ℕ → ℕ → F) (pt : ℕ → E) : E :=
  Φ.form (a.g pt) (a.ψ pt) W

/-- The law of an index atom on v variables: the multilinear extension of its values at the vertices
is, at every point, its tensor form at that point. -/
def IdxAtom.OK (a : IdxAtom E) (Φ : IdxFmt F) (v : ℕ) : Prop :=
  ∀ (W : ℕ → ℕ → F) (pt : ℕ → E), ext v (fun b => a.at Φ W (vtx v b)) pt = a.at Φ W pt

/-- The value of an atom of the first two kinds at the vertex b of a cube of v variables. -/
def Atom0.val (a : Atom0 E) (Φ : IdxFmt F) (v : ℕ) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    E :=
  match a with
  | .cell f => (f b).val A
  | .idx a => a.at Φ W (vtx v b)

/-- The value of a term, given the values of the atoms. -/
def Term.val (t : Term X E) (x : X) (b : ℕ) (Y : ℕ → E) : E := t.coef x b * (t.atoms.map Y).prod

def Poly0.val (P : Poly0 X E) (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    E :=
  (P.terms.map fun t => t.val x b fun j => (P.atom j).val Φ P.v W A b).sum

/-- The value of an atom at the vertex b of a cube of v variables. In a sum the vertex (b, j) of the
v + w variables has the number b · 2^w + j. -/
def Atom.val (a : Atom X E) (Φ : IdxFmt F) (v : ℕ) (x : X) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) (b : ℕ) : E :=
  match a with
  | .base a => a.val Φ v W A b
  | .sum w P => ∑ j ∈ range (2 ^ w), P.val Φ x W A (b * 2 ^ w + j)

/-- The value of a family at a vertex. -/
def Fam.val (f : Fam X E) (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) : E :=
  (f.terms.map fun t => t.val x b fun j => (f.atom j).val Φ f.v x W A b).sum

/-- The elements of a table. -/
def Tab.set (T : Tab F) : Set F := {u | ∃ k < 2 ^ T.T, T.t k = u}

/-- The conditions of a segment hold: every identity is 0 at every vertex, every key is (the image
of) an element of its table. -/
def SegSpec.Holds (S : SegSpec X F E) (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) :
    Prop :=
  (∀ f ∈ S.idn, ∀ b < 2 ^ f.v, f.val Φ x W A b = 0) ∧
  ∀ k ∈ S.keys, ∀ b < 2 ^ k.1.v, ∃ u ∈ k.2.set, k.1.val Φ x W A b = algebraMap F E u

end Val

/-! ## Well-formedness, and the places that are read -/

section WF
variable {X F E : Type}

/-- The places at which an atom of the first two kinds has a coefficient, at some vertex. -/
def Atom0.places (a : Atom0 E) (v : ℕ) : Set Place :=
  match a with
  | .cell f => {p | ∃ b < 2 ^ v, ∃ t ∈ (f b).terms, t.2 = p}
  | .idx _ => ∅

def Poly0.places (P : Poly0 X E) : Set Place := {p | ∃ j < P.na, p ∈ (P.atom j).places P.v}

def Atom.places (a : Atom X E) (v : ℕ) : Set Place :=
  match a with
  | .base a => a.places v
  | .sum _ P => P.places

/-- The places that a family reads. -/
def Fam.places (f : Fam X E) : Set Place := {p | ∃ j < f.na, p ∈ (f.atom j).places f.v}

/-- The places that a segment reads. -/
def SegSpec.places (S : SegSpec X F E) : Set Place :=
  {p | (∃ f ∈ S.idn, p ∈ f.places) ∨ ∃ k ∈ S.keys, p ∈ k.1.places}

variable [Field F] [Field E] [Algebra F E]

def Atom0.WF (a : Atom0 E) (Φ : IdxFmt F) (v : ℕ) : Prop :=
  match a with
  | .cell _ => True
  | .idx a => a.OK Φ v

/-- Terms name atoms below na; index atoms have their law. -/
def Poly0.WF (P : Poly0 X E) (Φ : IdxFmt F) : Prop :=
  (∀ t ∈ P.terms, ∀ j ∈ t.atoms, j < P.na) ∧ ∀ j < P.na, (P.atom j).WF Φ P.v

def Atom.WF (a : Atom X E) (Φ : IdxFmt F) (v : ℕ) : Prop :=
  match a with
  | .base a => a.WF Φ v
  | .sum w P => P.v = v + w ∧ P.WF Φ

/-- A family is well formed. -/
def Fam.WF (f : Fam X E) (Φ : IdxFmt F) : Prop :=
  (∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) ∧ ∀ j < f.na, (f.atom j).WF Φ f.v

def SegSpec.WF (S : SegSpec X F E) (Φ : IdxFmt F) : Prop :=
  (∀ f ∈ S.idn, f.WF Φ) ∧ ∀ k ∈ S.keys, k.1.WF Φ

end WF

/-! ## Integer matrices, read in E -/

namespace Partition
variable {F E : Type}

variable [Field F] [Field E] [Algebra F E]

/-- integer matrices, read in E -/
def castM (M : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → E := fun s r c => (M s r c : E)

end Partition

/-! ## Two small laws -/

namespace Spec

/-- States: the multilinear extension of a vector, at the point of a vertex b < 2^v, is the vector's
entry at b. -/
def ext_vtx : Prop :=
  ∀ (E : Type) [Field E] (v : ℕ) (f : ℕ → E) (b : ℕ), b < 2 ^ v → ext v f (vtx v b) = f b

/-- States: if `f.WF Φ`, the value of a family at a vertex b < 2^f.v depends on the matrices of
cells only at the places that it reads. -/
def fam_val_congr : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (f : Fam X E) (Φ : IdxFmt F) (x : X)
      (W : ℕ → ℕ → F) (A A' : ℕ → ℕ → ℕ → E),
    f.WF Φ → (∀ p ∈ f.places, A p.1 p.2.1 p.2.2 = A' p.1 p.2.1 p.2.2) →
    ∀ b < 2 ^ f.v, f.val Φ x W A b = f.val Φ x W A' b

end Spec
end Cb
