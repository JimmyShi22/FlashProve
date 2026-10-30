-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPart.lean: the polynomial meaning of a family of conditions; one reading of a block's
entries.

Arithmetisation for the sumchecks: a well-formed family of conditions, given by its values on the
Boolean cube, is extended to a polynomial (`Fam.ext`). The shared definitions of the files
Cb/Part/LdPart*.lean.
Definitions and statements (`Cb.Spec.ldPart_form` to
`Cb.Spec.ldPart_vtx`); the proofs are in Cb/Part/LdPartProofs.lean.
A family (`Fam`, Cb/Req/ReqSpec.lean) is a sum of terms: a public coefficient table (`Term.coef`)
times a product of atoms. An atom is affine in cells, linear in the index, or a sum over further
variables. The tensor form of a matrix is the bilinear form gᵀ · WE · eq(ψ, ·), for a vector g on
the rows and the equality vector of a column point ψ.

Why: Cb/Req/ReqSpec.lean gives a family its values at vertices (`Fam.val`). A sumcheck needs a
polynomial that has these values at the vertices, and maps whose values at a point are claimed. All
blocks that are built from a family must take the same polynomial; so it is defined once, here.
The index matrix is read in E. A block reads entries in E (`PscOur.F`,
Cb/Ld/LdPsc.lean), the index's among them. So the tensor form is written for a matrix WE over E
(`formE`); for the image of a matrix over F it is Cb/Gen/Tensor.lean's form (`Spec.ldPart_form`).

Main names:
  `Atom.ext`: an atom on v variables. Of the first two kinds: `Atom0.ext`. A sum atom is the
    multilinear extension of its values at the vertices b ↦ Σ_{j < 2^w} P.val (b, j) (in the Lean
    text: P.ext at the vertex b · 2^w + j of v + w variables: the same where P.v = v + w: see
    Limits), as in this protocol's technical report (lean/CREDITS.md; by inspection): in an outer
    summand it counts as one map of degree 1 in each variable. So all three kinds of atoms are
    multilinear: cell atoms and sum atoms by definition; index atoms by their law (`IdxAtom.OK`, a
    clause of well-formedness, carried from matrices over F to matrices over E: `Spec.ldPart_idx`).
    A claim on a sum atom at a point γ is the sum over all v + w variables of P's polynomial, under
    equality weights at γ on the v outer variables and plain weights on the w inner ones
    (`Spec.ldPart_sum`); the weights stand in the forms on the round polynomials, not in the
    summand, and add no degree.
  `LdPartRd E J`: one reading: how the entries that a block reads (J → E) are read as an index
    matrix over E and as matrices of cells in E. A letter without a law here: which entries, and how
    packed cells are unpacked, is the matter of the file that fills it, which owes: A reads entries
    of messages only, W entries of the index's matrix only, and a block's own masks are neither.
  `Spec.ldPart_idx`: an index atom with its law is, for all matrices WE over E and at all points,
    the multilinear extension of its values at the vertices. (The law speaks of matrices over F; the
    tensor form is E-linear in the matrix, and the unit matrices lie over F.)
  `Spec.ldPart_vtx`: at the vertices the polynomials have the values of Cb/Req/ReqSpec.lean: for a
    well-formed family f, all instances, matrices W over F and A, and b < 2^f.v:
    f.ext .. (vtx f.v b) = f.val Φ x W A b; the same for a well-formed atom, and for `Poly0` and
    `Atom0` without that premise.

Limits: this file says nothing on degrees (Cb/Part/LdPartPsc*.lean). A bound to that, at least:
`Spec.ldPart_idx` (index atoms with their law `IdxAtom.OK` are multilinear); `Atom0.ext`, `Atom.ext`
(cell atoms and sum atoms: by definition). `Atom.ext` feeds a sum atom's inner polynomial, which
works on P.v variables, vertices of v + w variables: right under well-formedness (P.v = v + w),
which whoever builds the further sumcheck must carry. Nothing on protocols. The option of the
technical report to replace an outer variable by γ's coordinate where the inner summand has degree
at most 1 in it (in every term at most one factor, the coefficient's table counted, depends on it)
is not rendered: all outer variables are summed.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqSpec

set_option autoImplicit false

namespace Cb

open Blocks Finset

section
variable {X E : Type} [Field E]

/-- the tensor form of a matrix over E with h rows and 2^k columns -/
def formE (h k : ℕ) (g ψ : ℕ → E) (WE : ℕ → ℕ → E) : E :=
  ∑ y ∈ range h, ∑ c ∈ range (2 ^ k), g y * eqN k 0 ψ c * WE y c

variable (h k : ℕ)

/-- An atom of the first two kinds on V variables, at a point q. Affine in cells: the multilinear
extension of its values at the vertices. Linear in the index: its tensor form at q. -/
def Atom0.ext (a : Atom0 E) (V : ℕ) (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) : E :=
  match a with
  | .cell f => Blocks.ext V (fun b => (f b).val A) q
  | .idx a => formE h k (a.g q) (a.ψ q) WE

/-- A term at a point, given the atoms' values: the multilinear extension of the coefficient table
on all V variables of its sum of terms, times the product of the atoms' values. -/
def Term.ext (t : Term X E) (V : ℕ) (x : X) (q : ℕ → E) (Y : ℕ → E) : E :=
  Blocks.ext V (t.coef x) q * (t.atoms.map Y).prod

/-- a sum of terms as a polynomial -/
def Poly0.ext (P : Poly0 X E) (x : X) (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) : E :=
  (P.terms.map fun t => t.ext P.v x q fun j => (P.atom j).ext h k P.v WE A q).sum

/-- An atom on v variables, at a point: a sum atom is the multilinear extension of its values at the
vertices (see Limits in the head). -/
def Atom.ext (a : Atom X E) (v : ℕ) (x : X) (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) : E :=
  match a with
  | .base a => a.ext h k v WE A q
  | .sum w P =>
    Blocks.ext v (fun b => ∑ j ∈ range (2 ^ w), P.ext h k x WE A (vtx (v + w) (b * 2 ^ w + j))) q

/-- The family as a polynomial. -/
def Fam.ext (f : Fam X E) (x : X) (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) : E :=
  (f.terms.map fun t => t.ext f.v x q fun j => (f.atom j).ext h k f.v x WE A q).sum

end

/-- One reading of a block's entries: an index matrix over E, matrices of cells in E. -/
structure LdPartRd (E J : Type) where
  W : (J → E) → ℕ → ℕ → E
  A : (J → E) → ℕ → ℕ → ℕ → E

namespace Spec

def ldPart_form : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (Φ : IdxFmt F) (g ψ : ℕ → E) (W : ℕ → ℕ → F),
    formE Φ.h (Φ.hi + Φ.lo) g ψ (fun y c => algebraMap F E (W y c)) = Φ.form g ψ W

/-- an index atom with its law is multilinear, at matrices over E -/
def ldPart_idx : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (Φ : IdxFmt F) (V : ℕ) (a : IdxAtom E),
    a.OK Φ V →
    ∀ (WE : ℕ → ℕ → E) (q : ℕ → E),
      Blocks.ext V (fun b => formE Φ.h (Φ.hi + Φ.lo) (a.g (vtx V b)) (a.ψ (vtx V b)) WE) q =
        formE Φ.h (Φ.hi + Φ.lo) (a.g q) (a.ψ q) WE

/-- what the claim on a sum atom says -/
def ldPart_sum : Prop :=
  ∀ (X E : Type) [Field E] (h k w : ℕ) (P : Poly0 X E) (v : ℕ) (x : X) (WE : ℕ → ℕ → E)
      (A : ℕ → ℕ → ℕ → E) (γ : ℕ → E),
    (Atom.sum w P).ext h k v x WE A γ =
      ∑ b ∈ range (2 ^ v),
        eqN v 0 γ b * ∑ j ∈ range (2 ^ w), P.ext h k x WE A (vtx (v + w) (b * 2 ^ w + j))

/-- Under the hypotheses below, at the vertices the polynomials have the values of
Cb/Req/ReqSpec.lean. -/
def ldPart_vtx : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (Φ : IdxFmt F) (x : X)
      (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ (a : Atom0 E) (V b : ℕ), b < 2 ^ V →
      a.ext Φ.h (Φ.hi + Φ.lo) V (fun y c => algebraMap F E (W y c)) A (vtx V b) = a.val Φ V W A b) ∧
    (∀ (P : Poly0 X E) (b : ℕ), b < 2 ^ P.v →
      P.ext Φ.h (Φ.hi + Φ.lo) x (fun y c => algebraMap F E (W y c)) A (vtx P.v b) =
        P.val Φ x W A b) ∧
    (∀ (a : Atom X E) (v b : ℕ), a.WF Φ v → b < 2 ^ v →
      a.ext Φ.h (Φ.hi + Φ.lo) v x (fun y c => algebraMap F E (W y c)) A (vtx v b) =
        a.val Φ v x W A b) ∧
    (∀ (f : Fam X E) (b : ℕ), f.WF Φ → b < 2 ^ f.v →
      f.ext Φ.h (Φ.hi + Φ.lo) x (fun y c => algebraMap F E (W y c)) A (vtx f.v b) = f.val Φ x W A b)

end Spec

end Cb
