-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSumFmt.lean: the numbers and the summand of a sumcheck for a family of conditions,
computed from the family's lists.

A family (`Fam`, Cb/Req/ReqSpec.lean) gives one value at each vertex of a cube, as a sum of terms
over atoms (`Atom`) of three kinds: affine in cells, an index atom, a sum.
Definitions and statements; the proofs are in Cb/Req/ReqSumFmtProofs.lean (`Fam.idx_lt`, `Fam.pp_lt`
are proved here). No protocol. Many statements of this library are written twice: a definition in
the namespace `Spec` states a proposition, and a theorem of the same name outside that namespace
proves it (lean/GLOSSARY.md).

The numbers:
  vector maps: number j is atom j. There are f.nc of them; that is f.na, or more if a term names an
    atom j ≥ f.na (it does not in a well-formed family, where f.nc = f.na by `Spec.nc_eq`).
  steps: `Req.summand`, in the steps of Cb/Req/ReqSumTerms.lean; f.nAux of them are auxiliary.
  degree: 1 + f.deg in each variable, computed from the lists.
  end set: all variables of the steps (j < f.nc + f.nAux: atoms, then auxiliary steps) but the atoms
    that are affine in cells: index atoms, sums, auxiliary steps (`Fam.inEnd`, `Fam.EndK`).
  masks: f.need = f.v · (f.deg + 1) + (size of the end set).

Main names:
  `Spec.summand_eq`, `Spec.summand_deg`: the law of the steps at arbitrary vectors; the degree
    bound. No hypothesis but that E is a field.
  `Spec.summand_corner`: at a vertex the summand is the sum of the terms at the entries of the
    vectors.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqSumCube
import Cb.Req.ReqSumTerms
import Blocks.StageMap
import Blocks.VecAppend

set_option autoImplicit false

namespace Cb
open Blocks Alg Finset Cb.Req

section
variable {X E : Type}

/-- A sum of terms over atoms of the first two kinds, as a family. -/
def Poly0.toFam (P : Poly0 X E) : Fam X E := ⟨P.v, P.na, fun j => .base (P.atom j), P.terms⟩

namespace Fam
variable (f : Fam X E)

/-- the lists of atoms of the terms -/
def lists : List (List ℕ) := f.terms.map Term.atoms

/-- The largest number of atoms in a term. -/
def deg : ℕ := maxLen f.lists

/-- the number of vector maps -/
def nc : ℕ := max f.na (maxAtom f.lists)

/-- the number of auxiliary steps -/
def nAux : ℕ := (auxAll f.nc f.lists).length

/-- The end set: every variable but the atoms that are affine in cells. -/
def inEnd (j : ℕ) : Bool :=
  if j < f.nc then
    match f.atom j with
    | .base (.cell _) => false
    | _ => true
  else true

/-- the end set, as a type -/
abbrev EndK : Type := {j : Fin (f.nc + f.nAux) // f.inEnd j.val = true}

/-- the number of end values -/
def nEnd : ℕ := Nat.count (fun j => f.inEnd j = true) (f.nc + f.nAux)

/-- The number of masks. -/
def need : ℕ := f.v * (f.deg + 1) + f.nEnd

theorem idx_lt {n : ℕ} (hn : f.need ≤ n) (i : Fin f.v) (j : Fin (f.deg + 1)) :
    i.val * (f.deg + 1) + j.val < n := by
  have h1 : (i.val + 1) * (f.deg + 1) ≤ f.v * (f.deg + 1) := Nat.mul_le_mul_right _ i.2
  have h2 : (i.val + 1) * (f.deg + 1) = i.val * (f.deg + 1) + (f.deg + 1) := by ring
  have h3 := j.2
  unfold need at hn
  omega

theorem pp_lt {n : ℕ} (hn : f.need ≤ n) (k : f.EndK) :
    f.v * (f.deg + 1) + Nat.count (fun j => f.inEnd j = true) k.1.val < n := by
  have h1 : Nat.count (fun j => f.inEnd j = true) k.1.val < f.nEnd :=
    Nat.count_strict_mono (p := fun j => f.inEnd j = true) k.2 k.1.2
  unfold need at hn
  omega

/-- the coefficients of the terms at a point: the extensions of the tables -/
def coefAt [Field E] (x : X) (pt : ℕ → E) (k : ℕ) : E :=
  (f.terms.map fun t => ext f.v (t.coef x) pt).getD k 0

end Fam
end

namespace Req
variable {X E : Type} [Field E]

/-- the summand at arbitrary vectors u_j -/
def summand (f : Fam X E) (x : X) (u : ℕ → (Fin f.v → Bool) → E) (z : Fin f.v → E) : E :=
  (Steps.mk f.nc f.nAux (stepsOf f.nc f.lists (f.coefAt x (nat z))).step).out fun j => mle (u j) z

end Req

namespace Spec
open Cb.Req

/-- In a family whose terms name atoms below na there are na vector maps. -/
def nc_eq : Prop :=
  ∀ (X E : Type) (f : Fam X E), (∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) → f.nc = f.na

/-- The law of the steps. -/
def summand_eq : Prop :=
  ∀ (X E : Type) [Field E] (f : Fam X E) (x : X) (u : ℕ → (Fin f.v → Bool) → E) (z : Fin f.v → E),
    Req.summand f x u z =
      (f.terms.map fun t =>
        ext f.v (t.coef x) (nat z) * (t.atoms.map fun j => mle (u j) z).prod).sum

/-- The degree. -/
def summand_deg : Prop :=
  ∀ (X E : Type) [Field E] (f : Fam X E) (x : X) (u : ℕ → (Fin f.v → Bool) → E),
    DegLE (fun _ => f.deg + 1) (Req.summand f x u)

/-- At a vertex the summand is the sum of terms at the entries of the vectors. -/
def summand_corner : Prop :=
  ∀ (X E : Type) [Field E] (f : Fam X E) (x : X)
      (u : ℕ → (Fin f.v → Bool) → E) (b : Fin f.v → Bool),
    Req.summand f x u (corner b) = (f.terms.map fun t => t.val x (num b) fun j => u j b).sum

end Spec
end Cb
