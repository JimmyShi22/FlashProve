-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscVarsMix.lean: one variable over a domain, then variables over the cube.

A sumcheck may treat several of its first variables as one variable that runs over a domain of E
(fewer rounds, a round polynomial of larger degree). With the definitions of Cb/Ld/LdPscVars.lean
that is a list of variables whose first is of a domain kind and whose others are of a cube kind.
Definitions and statements (`Cb.Spec.psm_*`); the proofs are in Cb/Ld/LdPscVarsMixProofs.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `pfSkip` n₁ n D k: the formats: degree n₁ in the first variable, n in the k others.
  `pdSkip` n₁ n dom k: plain sums: over the domain, then over the cube (`Spec.psm_sum`).
  `pdSkipW` n₁ n dom z₀ k z: weighted sums: Lagrange weights at z₀, then equality weights at z
    (`Spec.psm_sumW`).
  `pvExt` dom u x₀ z: the extension of a table u on (domain × cube): Lagrange in the first
    coordinate, multilinear in the others.
  `Spec.psm_ext_at`: if the domain's points are distinct, the extension extends the table.
  `Spec.psm_ext_deg`: if the domain's points are distinct and there is one, in its first coordinate
    the extension is a polynomial with as many coefficients as the domain has points.
  `Spec.psm_ext_lin`: in the other coordinates the extension is the multilinear extension of the
    table's rows combined.
  `Spec.psm_ext_sum`: if the domain's points are distinct, the value of the extension at (z₀, z) is
    a sum over the weighted variables at (z₀, z), of the extension itself: a claim on a value is a
    sum claim.
  `Spec.psm_ok`, `Spec.psm_okW`: every variable meets the condition (sum of ψ) = 1 (`HVar.OK`,
    Cb/Ld/LdHide.lean); for the plain sums if n ≥ 1 and the domain's size is not 0 in E, for the
    weighted sums if the domain's points are distinct and there is one. (ψ of each kind, with these
    conditions: the head of Cb/Ld/LdPscVars.lean.)

Notation:
  `n₁`, `n`: natural numbers; in `pfDom E n₁ D`, `pfCube E n` (Cb/Ld/LdPscVars.lean) the field `n`
    of `PFmt` (Cb/Ld/LdPsc.lean): the largest degree of a round polynomial.
  `D`, `dom`: a domain is a finite type D of names with a map dom : D → E (the head of
    Cb/Ld/LdPscVars.lean).
  ψ: the field `psi : Fin (n + 1) → R` of a variable (`HVar`, Cb/Ld/LdHide.lean): the public
    polynomial that fills the place of this variable in the earlier terms (of `hU`, in that file).
  `v.OK`: `v.phi v.psi = 1` (`HVar.OK`, Cb/Ld/LdHide.lean).
  `hSumAll`: the sum over all variables (Cb/Ld/LdHide.lean).
  `ppOf`, `hFnOf`: a point from a function on the variables, and back (Cb/Ld/LdPscVars.lean).
  `pH l d`: a map from `PPt l` to `HPt (pVars l d)` (Cb/Ld/LdPsc.lean).
  `Alg.corner b`: a vertex of the cube as a point of K^ι (Alg/Mle.lean).

Limits: nothing is asked of the domain but distinct points, at least one point for `Spec.psm_okW`
and `Spec.psm_ext_deg`, and, for plain sums, a size that is not 0 in E. Which degree n₁ a given
summand needs is not said here. A summand of degree δ in the table's values has degree
δ · (size - 1) in the first variable; ψ adds nothing, being constant. This file says nothing on any
protocol.
-/
import Cb.Ld.LdPscVars

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

section
variable (E : Type) [Field E] [Fintype E] {D : Type} [Fintype D]

@[reducible] def pfSkip (n₁ n : ℕ) (D : Type) [Fintype D] (k : ℕ) : List (PFmt E) :=
  pfDom E n₁ D :: List.replicate k (pfCube E n)

def pdSkip (n₁ n : ℕ) (dom : D → E) (k : ℕ) : PDats (pfSkip E n₁ n D k) :=
  (pdDom E n₁ dom, pdPlains E n k)
def pdSkipW [DecidableEq D] (n₁ n : ℕ) (dom : D → E) (z₀ : E) (k : ℕ) (z : Fin k → E) :
    PDats (pfSkip E n₁ n D k) :=
  (pdLag E n₁ dom z₀, pdEqs E n k z)

/-- The extension of a table u on (domain × cube): Lagrange in the first coordinate, multilinear in
the others. -/
def pvExt [DecidableEq D] {k : ℕ} (dom : D → E) (u : D → (Fin k → Bool) → E)
    (x₀ : E) (z : Fin k → E) : E :=
  ∑ x, (Lagrange.basis Finset.univ dom x).eval x₀ * Alg.mle (u x) z

end

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

def psm_ok : Prop :=
  ∀ (n₁ n k : ℕ) (D : Type) [Fintype D] (dom : D → E),
    1 ≤ n → (Fintype.card D : E) ≠ 0 → ∀ v ∈ pVars (pfSkip E n₁ n D k) (pdSkip E n₁ n dom k), v.OK
def psm_okW : Prop :=
  ∀ (n₁ n k : ℕ) (D : Type) [Fintype D] [DecidableEq D] [Nonempty D] (dom : D → E)
      (z₀ : E) (z : Fin k → E),
    Function.Injective dom → ∀ v ∈ pVars (pfSkip E n₁ n D k) (pdSkipW E n₁ n dom z₀ k z), v.OK

/-- The sum over the variables of `pdSkip`, of any f, is the sum of f over the domain, then
over the cube. -/
def psm_sum : Prop :=
  ∀ (n₁ n k : ℕ) (D : Type) [Fintype D] (dom : D → E)
      (f : HPt (pVars (pfSkip E n₁ n D k) (pdSkip E n₁ n dom k)) → E),
    hSumAll (pVars (pfSkip E n₁ n D k) (pdSkip E n₁ n dom k)) f =
      ∑ x, ∑ b : Fin k → Bool, f (dom x, pH _ (pdPlains E n k) (ppOf (pfCube E n) k (Alg.corner b)))

/-- The sum over the variables of `pdSkipW`, of any f, is the sum of f over the domain and
the cube, with the Lagrange weights at z₀ and the equality weights at z. -/
def psm_sumW : Prop :=
  ∀ (n₁ n k : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E) (z₀ : E) (z : Fin k → E)
      (f : HPt (pVars (pfSkip E n₁ n D k) (pdSkipW E n₁ n dom z₀ k z)) → E),
    hSumAll (pVars (pfSkip E n₁ n D k) (pdSkipW E n₁ n dom z₀ k z)) f =
      ∑ x, ∑ b : Fin k → Bool, (Lagrange.basis Finset.univ dom x).eval z₀ *
        (Alg.eqk z b * f (dom x, pH _ (pdEqs E n k z) (ppOf (pfCube E n) k (Alg.corner b))))

/-- If the domain's points are distinct, the extension extends the table. -/
def psm_ext_at : Prop :=
  ∀ (k : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E) (u : D → (Fin k → Bool) → E)
      (x : D) (b : Fin k → Bool),
    Function.Injective dom → pvExt E dom u (dom x) (Alg.corner b) = u x b

/-- If the domain's points are distinct and there is one, in its first coordinate the
extension is a polynomial with as many coefficients as the domain has points. -/
def psm_ext_deg : Prop :=
  ∀ (k m : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E)
      (u : D → (Fin k → Bool) → E) (z : Fin k → E),
    Function.Injective dom → Fintype.card D = m + 1 →
    ∃ c : Fin (m + 1) → E, ∀ x₀, pvExt E dom u x₀ z = hev c x₀

/-- In the other coordinates the extension is the multilinear extension of the table's rows
combined. -/
def psm_ext_lin : Prop :=
  ∀ (k : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E) (u : D → (Fin k → Bool) → E)
      (x₀ : E) (z : Fin k → E),
    pvExt E dom u x₀ z =
      Alg.mle (fun b => ∑ x, (Lagrange.basis Finset.univ dom x).eval x₀ * u x b) z

/-- If the domain's points are distinct, the value of the extension at (z₀, z) is a sum over the
weighted variables at (z₀, z), of the extension itself: a claim on a value is a sum claim. -/
def psm_ext_sum : Prop :=
  ∀ (n₁ n k : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E) (z₀ : E)
      (z : Fin k → E) (u : D → (Fin k → Bool) → E),
    Function.Injective dom →
    hSumAll (pVars (pfSkip E n₁ n D k) (pdSkipW E n₁ n dom z₀ k z))
        (fun X => pvExt E dom u X.1 (hFnOf (pfCube E n) k (pdEqs E n k z) X.2)) =
      pvExt E dom u z₀ z

end
end Spec
end
end Cb
