-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqFamTuple.lean: a tuple of families of identities as one family with drawn coefficients.

A linear combination of constraint systems over Boolean cubes, one coefficient for each, written as
one system whose instance has the coefficients. A family (`Fam`, Cb/Req/ReqSpec.lean) gives one
value at each vertex b < 2^v of a cube; a family of identities has to be 0 at every vertex.
Definitions and statements on data; the proofs are in Cb/Req/ReqFamTupleProofs.lean. No protocol.

Why: a zerocheck on a tuple of polynomial maps on one cube: the verifier draws one point and one
coefficient z_t for each map, and what is left is one sum claim on the summand ∑_t z_t g_t. (Where
a print of this protocol's technical report (lean/CREDITS.md) has a tuple, and that its
preamble of a request has ONE map a segment and names no coefficient there, is a reading made by
others; it was not read for this file.)
A family of Cb/Req/ReqSpec.lean has coefficient tables that read the instance
(`Term.coef : X → ℕ → E`). So the combined family is a family over the larger instance `XZ X E` = X
× (ℕ → E).

Main names (the statements are in `Cb.Spec`):
  `famT L`: the combined family of L = [f_0, .., f_(n-1)]: ∑_t (the constant table z_t) · (f_t, read
    at x, brought to V = max v_t variables), side by side (`Fam.add`, Cb/Req/ReqGlue.lean). V
    variables: no selector variable (unlike `Fam.glue`, Cb/Req/ReqGlue.lean). A family on fewer
    variables reads the low bits of a vertex (`Fam.to`, Cb/Req/ReqGlue.lean): this is this library's
    layout of smaller cubes in the large one; it repeats the family's values 2^(V - v_t) times.
  `famT_val`: if every family of L is well formed (`Fam.WF`), its value at the instance (x, z) and
    the vertex b: ∑_t z_t · (value of f_t at x and b mod 2^(v_t)).
  `famT_valTo`: the same, under the same premise, with each family brought to the large cube.
  `degLe_famT`, `to_zero_iff`, `low_zero_iff`, `tuple_zero_iff`: see their docstrings.

Limits: this file says nothing on the zerocheck.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqGlue
import Cb.Req.ReqNumsGlue

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

section Defs
variable {X X' E : Type}

def Term.reX (π : X' → X) (t : Term X E) : Term X' E := ⟨fun x' b => t.coef (π x') b, t.atoms⟩

def Poly0.reX (π : X' → X) (P : Poly0 X E) : Poly0 X' E :=
  ⟨P.v, P.na, P.atom, P.terms.map (Term.reX π)⟩

def Atom.reX (π : X' → X) : Atom X E → Atom X' E
  | .base a => .base a
  | .sum w P => .sum w (P.reX π)

/-- A family over another type of instances. -/
def Fam.reX (π : X' → X) (f : Fam X E) : Fam X' E :=
  ⟨f.v, f.na, fun j => (f.atom j).reX π, f.terms.map (Term.reX π)⟩

/-- an instance together with coefficients -/
abbrev XZ (X E : Type) : Type := X × (ℕ → E)

/-- the families from number t on, each with its coefficient -/
def tupFrom [Zero E] [Mul E] (V : ℕ) : ℕ → List (Fam X E) → Fam (XZ X E) E
  | _, [] => Fam.pub V fun _ _ => 0
  | t, f :: L =>
    Fam.add (Fam.mask (fun x' _ => x'.2 t) ((f.reX Prod.fst).to V)) (tupFrom V (t + 1) L)

/-- The combined family. (Its number of variables is written out, so that it is `maxV L` by
definition; the rest is `tupFrom (maxV L) 0 L`: `famT_eq`, Cb/Req/ReqFamTupleProofs.lean.) -/
def famT [Zero E] [Mul E] (L : List (Fam X E)) : Fam (XZ X E) E :=
  ⟨maxV L, (tupFrom (maxV L) 0 L).na, (tupFrom (maxV L) 0 L).atom, (tupFrom (maxV L) 0 L).terms⟩

/-- what its value is to be: the sum of coefficient times value, from number t on -/
def tupVal [Zero E] [Add E] [Mul E] (val : Fam X E → E) (z : ℕ → E) : ℕ → List (Fam X E) → E
  | _, [] => 0
  | t, f :: L => z t * val f + tupVal val z (t + 1) L

end Defs

namespace Spec

def reX_val : Prop :=
  ∀ (X X' F E : Type) [Field F] [Field E] [Algebra F E] (π : X' → X) (f : Fam X E) (Φ : IdxFmt F)
      (x' : X') (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ),
    (f.reX π).val Φ x' W A b = f.val Φ (π x') W A b

def reX_wf : Prop :=
  ∀ (X X' F E : Type) [Field F] [Field E] [Algebra F E] (π : X' → X) (f : Fam X E) (Φ : IdxFmt F),
    f.WF Φ → (f.reX π).WF Φ

def reX_places : Prop := ∀ (X X' E : Type) (π : X' → X) (f : Fam X E), (f.reX π).places = f.places

def degLe_reX : Prop :=
  ∀ (X X' E : Type) (π : X' → X) (f : Fam X E) (d : ℕ), f.DegLe d → (f.reX π).DegLe d

def famT_v : Prop := ∀ (X E : Type) [Zero E] [Mul E] (L : List (Fam X E)), (famT L).v = maxV L

/-- The value of the combined family. -/
def famT_val : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (Φ : IdxFmt F) (x : X)
      (z : ℕ → E) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ L, f.WF Φ) →
    ∀ b, (famT L).val Φ (x, z) W A b =
      ∑ t : Fin L.length, z t.val * (L.get t).val Φ x W A (b % 2 ^ (L.get t).v)

/-- the same, with each family brought to the large cube -/
def famT_valTo : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (Φ : IdxFmt F) (x : X)
      (z : ℕ → E) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ L, f.WF Φ) →
    ∀ b, (famT L).val Φ (x, z) W A b =
      ∑ t : Fin L.length, z t.val * ((L.get t).to (maxV L)).val Φ x W A b

def famT_wf : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (Φ : IdxFmt F),
    (∀ f ∈ L, f.WF Φ) → (famT L).WF Φ

def famT_places : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (Φ : IdxFmt F),
    (∀ f ∈ L, f.WF Φ) → ∀ p, p ∈ (famT L).places ↔ ∃ f ∈ L, p ∈ f.places

/-- States: if every family of L has `DegLe d` (Cb/Req/ReqNumsGlue.lean), so has the combined
family: the coefficients add no atom to a term. -/
def degLe_famT : Prop :=
  ∀ (X E : Type) [Zero E] [Mul E] (L : List (Fam X E)) (d : ℕ),
    (∀ f ∈ L, f.DegLe d) → (famT L).DegLe d

/-- a vector on a small cube vanishes iff, read at the low bits, it vanishes on a larger cube -/
def low_zero_iff : Prop :=
  ∀ (E : Type) [Zero E] (v V : ℕ) (h : ℕ → E),
    v ≤ V → ((∀ b < 2 ^ v, h b = 0) ↔ ∀ b < 2 ^ V, h (b % 2 ^ v) = 0)

/-- a well-formed family brought to more variables vanishes on the large cube iff the family
vanishes on its own -/
def to_zero_iff : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (f : Fam X E) (Φ : IdxFmt F) (V : ℕ) (x : X)
      (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    f.WF Φ → f.v ≤ V →
    ((∀ b < 2 ^ V, (f.to V).val Φ x W A b = 0) ↔ ∀ b < 2 ^ f.v, f.val Φ x W A b = 0)

/-- All families vanish on their cubes iff each, read at the low bits, vanishes on the large cube.
-/
def tuple_zero_iff : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (L : List (Fam X E)) (Φ : IdxFmt F) (x : X)
      (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ L, ∀ b < 2 ^ f.v, f.val Φ x W A b = 0) ↔
    ∀ (t : Fin L.length), ∀ b < 2 ^ maxV L, (L.get t).val Φ x W A (b % 2 ^ (L.get t).v) = 0

end Spec
end Cb
