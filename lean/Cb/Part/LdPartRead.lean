-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartRead.lean: readings: a claim on a cell atom at a point, as weights on rows times
weights on columns.

Definitions and one statement (`Cb.Spec.ldPartRead_byCol`); the proof is in
Cb/Part/LdPartReadProofs.lean. Generic: any field; nothing here knows a model or a protocol. In
standard terms: after a sumcheck, a claim on the multilinear extension of an affine function of
cells is written as a constant plus a sum of bilinear forms (weights on rows, a segment's matrix,
weights on columns).

Why: a sumcheck on a family of conditions (Cb/Req/ReqSpec.lean) leaves, for each atom that is affine
in cells, the claim "the multilinear extension of the atom's values, at the point γ, is v". The read
stage (`ReadCl`, `readsOf`, Cb/Ld/LdRead.lean) takes claims of one form:
constant + Σ_k Σ_c cw k c · (Σ_r W k r · Y r c) + masks = target: reads (a vector of weights on the
rows of the matrix of cells, applied to all columns) and coefficients on the entries of the reads.
The same notions are in Cm/TargetRead.lean, beside the model, with a second statement on atoms that
are given by bits. The folder Cb is below Cm in the order of imports, so what the builder of a
request needs is carried over here, under names of its own.

Main names:
  `LdPartRg`: a reading: a constant (a function of γ) and a list of items (`LdPartItem`).
  `ρ.Of R C v f`: see its docstring.
  `Spec.ldPartRead_byCol`: every atom all of whose places lie in the shapes, in segments below n,
    has the reading `ldPartByCol n C v f`. So (Cb/Part/LdPartNmOf.lean, `Spec.ldPartNmOf_reading`,
    under its hypotheses) a builder of a request has a list of reads for every partition; its length
    is the number of columns.

Limits: this file does not say that reads are few, or shared. It does not say whose matrices are
read: items name this or an earlier segment alike. It says nothing on protocols, errors or cost.
How this stands to a write-up of ours (lean/CREDITS.md; by reading, not machine-checked, of the file
beside the model):
`ldPartByCol` has no counterpart there.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req.ReqSpec

set_option autoImplicit false

namespace Cb
open Blocks Finset

variable {E : Type} [Field E]

/-- One item of a reading. -/
structure LdPartItem (E : Type) where
  seg : ℕ
  row : (ℕ → E) → ℕ → E
  col : (ℕ → E) → ℕ → E

/-- The item's value at the matrices A, in the shapes R (rows), C (columns). -/
def LdPartItem.val (t : LdPartItem E) (R C : ℕ → ℕ) (γ : ℕ → E) (A : ℕ → ℕ → ℕ → E) : E :=
  ∑ r ∈ range (R t.seg), ∑ c ∈ range (C t.seg), t.row γ r * t.col γ c * A t.seg r c

/-- A reading. -/
structure LdPartRg (E : Type) where
  k0 : (ℕ → E) → E
  items : List (LdPartItem E)

/-- Says: ρ is a reading of the atom f on v variables. -/
def LdPartRg.Of (ρ : LdPartRg E) (R C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E) : Prop :=
  ∀ (A : ℕ → ℕ → ℕ → E) (γ : ℕ → E),
    ext v (fun b => (f b).val A) γ = ρ.k0 γ + (ρ.items.map fun t => t.val R C γ A).sum

/-- the coefficient of an affine form at a place -/
def ldPartCoefAt (g : CForm E) (q : Place) : E :=
  (g.terms.map fun t => if t.2 = q then t.1 else 0).sum

/-- The reading with one item for each column; `Spec.ldPartRead_byCol` states that it is a reading
(`LdPartRg.Of`) of the atoms that meet its premise. -/
def ldPartByCol (n : ℕ) (C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E) : LdPartRg E where
  k0 := fun γ => ext v (fun b => (f b).c0) γ
  items := (List.range n).flatMap fun s => (List.range (C s)).map fun c =>
    ⟨s, fun γ r => ext v (fun b => ldPartCoefAt (f b) (s, r, c)) γ,
      fun _ c' => if c' = c then 1 else 0⟩

/-- States: every atom all of whose places lie in the shapes, in segments below n, has the reading
`ldPartByCol n C v f`. -/
def Spec.ldPartRead_byCol : Prop :=
  ∀ (E : Type) [Field E] (n : ℕ) (R C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E),
    (∀ b < 2 ^ v, ∀ t ∈ (f b).terms, t.2.1 < n ∧ t.2.2.1 < R t.2.1 ∧ t.2.2.2 < C t.2.1) →
    (ldPartByCol n C v f).Of R C v f

end Cb
