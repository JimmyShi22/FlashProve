-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscVars.lean: variables for the sumcheck for a polynomial summand (Cb/Ld/LdPsc.lean).

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdPscVarsProofs.lean.
A variable of Cb/Ld/LdPsc.lean is a format (`PFmt`: degree, names of nodes, challenge set) and data
(`PDat`: nodes, weights, ψ), which may depend on the state. ψ is the polynomial that fills the place
of this variable in the earlier terms of `hU` (`HVar.psi`, Cb/Ld/LdHide.lean). Here are four kinds
of "sum over a variable".

Main names:
  plain: format `pfCube`, data `pdPlain`; the sum of g is g(0) + g(1); ψ = X (needs n ≥ 1).
  equality-weighted at z: format `pfCube`, data `pdEq`; the sum of g is (1 - z) g(0) + z g(1);
    ψ = 1.
  domain: format `pfDom`, data `pdDom`; the sum of g is ∑ over x in the domain of g(x);
    ψ = 1 / (size of the domain) (the size must not be 0 in E).
  Lagrange-weighted at z: format `pfDom`, data `pdLag`; the sum of g is ∑ over x in the domain of
    Lag_x(z) g(x); ψ = 1 (the domain's points are distinct, and the domain is not empty).
  A fifth kind, the dummy variable with the sum g(0) and ψ = 1, is in Cb/Ld/LdPsc.lean:
    `pDummy`, `pDummyD`.
  A domain is a finite type D of names with a map dom : D → E. Lag_x is the Lagrange basis
    polynomial of the domain at x (Mathlib's Lagrange.basis).
  For each kind the one condition on a variable, (sum of ψ) = 1, holds under the condition in its
    row's brackets (`Spec.psv_plain_ok`, `Spec.psv_eq_ok`, `Spec.psv_dom_ok`, `Spec.psv_lag_ok`).
  `Spec.psv_eqs_mle`: by it a claim "multilinear extension at z = v" is a sum claim, the input form
    of a sumcheck.

Why the weighted kinds: `Spec.psv_eq_lin`: the equality-weighted sum of a polynomial of degree at
most 1 is its value at z. `Spec.psv_lag_eval`: if the domain's points are distinct, the
Lagrange-weighted sum of a polynomial with at most as many coefficients as the domain has points is
its value at z.

Notation: `n`: the largest degree of a round polynomial; `f.var d`: the variable of a format f and
data d, as an `HVar` of Cb/Ld/LdHide.lean; `v.sum g`: the "sum" of a function g: a weighted sum of
values at nodes; `v.OK`: `v.phi v.psi = 1` (Cb/Ld/LdHide.lean); `hev c x`: the value of a
polynomial, given by its coefficients; `hSumAll`: the sum over all variables; `HPt`: points
(Cb/Ld/LdHide.lean); `PPt`: points, without the data (Cb/Ld/LdPsc.lean); `pVars l d`: the variables
(`List (HVar E)`) of the formats l with the data d; `pH l d`: a map from `PPt l` to
`HPt (pVars l d)`. (`PFmt`, `PFmt.var`, `pVars`, `pH`: Cb/Ld/LdPsc.lean; `HVar.sum`, `HVar.OK`,
`hev`, `hSumAll`: Cb/Ld/LdHide.lean.)

Limits: this file says nothing on any protocol. A functional that is no weighted sum of values (a
vector-valued one, say) is not covered. This file says nothing on which of the kinds may share a
verifier message with the coefficient of the sumcheck (ε, the verifier's message of round 0:
Cb/Ld/LdPsc.lean).
-/
import Cb.Ld.LdPsc
import Alg.Mle
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

section Kinds
variable (E : Type) [Field E] [Fintype E]

/-- formats: nodes named by Bool; nodes named by D.  Challenges from all of E. -/
@[reducible] def pfCube (n : ℕ) : PFmt E := { n := n, S := Bool, Ch := E, val := id }
@[reducible] def pfDom (n : ℕ) (D : Type) [Fintype D] : PFmt E :=
  { n := n, S := D, Ch := E, val := id }

/-- the constant polynomial c, and X, as vectors of coefficients -/
def pvConst (n : ℕ) (c : E) : Fin (n + 1) → E := fun t => if (t : ℕ) = 0 then c else 0
def pvX (n : ℕ) : Fin (n + 1) → E := fun t => if (t : ℕ) = 1 then 1 else 0

/-- plain: g(0) + g(1), ψ = X -/
def pdPlain (n : ℕ) : PDat E (pfCube E n) :=
  { node := fun b => if b then 1 else 0, wt := fun _ => 1, psi := pvX E n }
/-- equality-weighted at z: (1 - z) g(0) + z g(1), ψ = 1 -/
def pdEq (n : ℕ) (z : E) : PDat E (pfCube E n) :=
  { node := fun b => if b then 1 else 0,
    wt := fun b => if b then z else 1 - z, psi := pvConst E n 1 }

variable {D : Type} [Fintype D]

/-- domain: the sum over the domain, ψ = 1 / size -/
def pdDom (n : ℕ) (dom : D → E) : PDat E (pfDom E n D) :=
  { node := dom, wt := fun _ => 1, psi := pvConst E n (Fintype.card D : E)⁻¹ }
/-- Lagrange-weighted at z, ψ = 1 -/
def pdLag [DecidableEq D] (n : ℕ) (dom : D → E) (z : E) : PDat E (pfDom E n D) :=
  { node := dom, wt := fun x => (Lagrange.basis Finset.univ dom x).eval z, psi := pvConst E n 1 }

/-- k plain variables; k equality-weighted variables at a point -/
def pdPlains (n : ℕ) : (k : ℕ) → PDats (List.replicate k (pfCube E n))
  | 0 => ()
  | k + 1 => (pdPlain E n, pdPlains n k)
def pdEqs (n : ℕ) : (k : ℕ) → (Fin k → E) → PDats (List.replicate k (pfCube E n))
  | 0, _ => ()
  | k + 1, z => (pdEq E n (z 0), pdEqs n k fun i => z i.succ)

end Kinds

section Points
variable {E : Type}

/-- a point from a function on the variables, and back -/
def ppOf (f : PFmt E) : (k : ℕ) → (Fin k → E) → PPt (List.replicate k f)
  | 0, _ => ()
  | k + 1, x => (x 0, ppOf f k fun i => x i.succ)
def hFnOf (f : PFmt E) :
    (k : ℕ) → (d : PDats (List.replicate k f)) → HPt (pVars (List.replicate k f) d) → Fin k → E
  | 0, _, _ => Fin.elim0
  | k + 1, d, X => Fin.cons X.1 (hFnOf f k d.2 X.2)

end Points

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- States: the plain variable is the one of Cb/Ld/LdHide.lean (`HVar.plain`). -/
def psv_plain_var : Prop := ∀ n : ℕ, (pfCube E n).var (pdPlain E n) = HVar.plain E n

def psv_plain_sum : Prop :=
  ∀ (n : ℕ) (g : E → E), ((pfCube E n).var (pdPlain E n)).sum g = g 0 + g 1
def psv_plain_ok : Prop := ∀ n : ℕ, 1 ≤ n → ((pfCube E n).var (pdPlain E n)).OK

def psv_eq_sum : Prop :=
  ∀ (n : ℕ) (z : E) (g : E → E), ((pfCube E n).var (pdEq E n z)).sum g = (1 - z) * g 0 + z * g 1
def psv_eq_ok : Prop := ∀ (n : ℕ) (z : E), ((pfCube E n).var (pdEq E n z)).OK
/-- States: the equality-weighted sum of a polynomial of degree at most 1 is its value at z. -/
def psv_eq_lin : Prop :=
  ∀ (n : ℕ) (z c₀ c₁ : E), ((pfCube E n).var (pdEq E n z)).sum (fun x => c₀ + c₁ * x) = c₀ + c₁ * z

def psv_dom_sum : Prop :=
  ∀ (n : ℕ) (D : Type) [Fintype D] (dom : D → E) (g : E → E),
    ((pfDom E n D).var (pdDom E n dom)).sum g = ∑ x, g (dom x)
def psv_dom_ok : Prop :=
  ∀ (n : ℕ) (D : Type) [Fintype D] (dom : D → E),
    (Fintype.card D : E) ≠ 0 → ((pfDom E n D).var (pdDom E n dom)).OK

def psv_lag_sum : Prop :=
  ∀ (n : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E) (z : E) (g : E → E),
    ((pfDom E n D).var (pdLag E n dom z)).sum g =
      ∑ x, (Lagrange.basis Finset.univ dom x).eval z * g (dom x)
def psv_lag_ok : Prop :=
  ∀ (n : ℕ) (D : Type) [Fintype D] [DecidableEq D] [Nonempty D] (dom : D → E) (z : E),
    Function.Injective dom → ((pfDom E n D).var (pdLag E n dom z)).OK
/-- States: if the domain's points are distinct, at a point of the domain the weights pick that
point. -/
def psv_lag_at : Prop :=
  ∀ (n : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E) (x₀ : D) (g : E → E),
    Function.Injective dom → ((pfDom E n D).var (pdLag E n dom (dom x₀))).sum g = g (dom x₀)
/-- States: if the domain's points are distinct, the Lagrange-weighted sum of a polynomial with at
most as many coefficients as the domain has points is its value at z. -/
def psv_lag_eval : Prop :=
  ∀ (n m : ℕ) (D : Type) [Fintype D] [DecidableEq D] (dom : D → E) (z : E) (c : Fin (m + 1) → E),
    Function.Injective dom → m + 1 ≤ Fintype.card D →
    ((pfDom E n D).var (pdLag E n dom z)).sum (hev c) = hev c z

/-- States: different challenges have different values. -/
def psv_val : Prop :=
  (∀ n : ℕ, Function.Injective (pfCube E n).val) ∧
  ∀ (n : ℕ) (D : Type) [Fintype D], Function.Injective (pfDom E n D).val

/-- These state, of the lists: every variable meets the condition (the plain ones for n ≥ 1). -/
def psv_plains_ok : Prop :=
  ∀ n k : ℕ, 1 ≤ n → ∀ v ∈ pVars (List.replicate k (pfCube E n)) (pdPlains E n k), v.OK
def psv_eqs_ok : Prop :=
  ∀ (n k : ℕ) (z : Fin k → E), ∀ v ∈ pVars (List.replicate k (pfCube E n)) (pdEqs E n k z), v.OK

/-- States: `hFnOf` takes the point that `ppOf` makes from a function back to that function. -/
def psv_fn_pt : Prop :=
  ∀ (f : PFmt E) (k : ℕ) (d : PDats (List.replicate k f)) (x : Fin k → E),
    hFnOf f k d (pH (List.replicate k f) d (ppOf f k x)) = x

/-- States: the sum over k plain variables is the sum over the cube. -/
def psv_plains_sum : Prop :=
  ∀ (n k : ℕ) (f : HPt (pVars (List.replicate k (pfCube E n)) (pdPlains E n k)) → E),
    hSumAll (pVars (List.replicate k (pfCube E n)) (pdPlains E n k)) f =
      ∑ b : Fin k → Bool, f (pH _ (pdPlains E n k) (ppOf (pfCube E n) k (Alg.corner b)))

/-- States: the sum over k equality-weighted variables at z is the sum over the cube with the
weights eq(z, b). -/
def psv_eqs_sum : Prop :=
  ∀ (n k : ℕ) (z : Fin k → E) (f : HPt (pVars (List.replicate k (pfCube E n)) (pdEqs E n k z)) → E),
    hSumAll (pVars (List.replicate k (pfCube E n)) (pdEqs E n k z)) f =
      ∑ b : Fin k → Bool,
        Alg.eqk z b * f (pH _ (pdEqs E n k z) (ppOf (pfCube E n) k (Alg.corner b)))

/-- States: the value of a multilinear extension at z is a sum over k equality-weighted variables at
z, of the extension itself. -/
def psv_eqs_mle : Prop :=
  ∀ (n k : ℕ) (z : Fin k → E) (u : (Fin k → Bool) → E),
    hSumAll (pVars (List.replicate k (pfCube E n)) (pdEqs E n k z))
        (fun X => Alg.mle u (hFnOf (pfCube E n) k (pdEqs E n k z) X)) = Alg.mle u z

end
end Spec
end
end Cb
