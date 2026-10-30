-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHide.lean: the one hiding polynomial of a zero-knowledge sumcheck.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdHideProofs.lean. The file
follows the paper that this protocol builds on (lean/CREDITS.md).

A sumcheck in the variables X_1 .. X_k is made zero knowledge by adding one random polynomial to the
summand (what this file states of it: `Spec.hide_pass`, `Spec.hide_law`, under their hypotheses; no
protocol). The polynomial is a sum of k + 1 terms,
      U(X) = W_1(X_1) ψ_2(X_2) .. ψ_k(X_k) + W_2(X_2) ψ_3(X_3) .. ψ_k(X_k) + .. + W_k(X_k) + c,
where W_l is a univariate polynomial without constant term, of degree at most n_l, c is a constant,
and the ψ_j are fixed public polynomials. It has only 1 + n_1 + .. + n_k coefficients, and yet its
sumcheck messages are as random as sumcheck messages can be: the map from the coefficients to (the
sum, the k round polynomials) is, at every point γ of challenges, a bijection onto the set of all
consistent messages, if every variable has `HVar.OK` (below).

R is a commutative ring (challenges, public polynomials), M an R-module (values, round
polynomials). A variable (`HVar`) has: n (a round polynomial has the n + 1 coefficients of
1, X, .., X^n); a "sum" over the variable, which is any weighted sum of values,
φ(g) = ∑_s wt s • g(node s) (narrower than "any linear functional on polynomials"; sums over the
cube or over a domain, with or without weights, and the value at one point are of this kind); and
ψ, with the one condition φ(ψ) = 1 (`HVar.OK`). The plain variable (`HVar.plain`):
φ(g) = g(0) + g(1), ψ = X, which needs n ≥ 1. The variables of a sumcheck are a list, and all
notions go by recursion on it.
Coefficients are named by `HIdx l` (for the list v :: l: the n coefficients of X, .., X^n of the
first term, then those of l; for the empty list: the constant). In the paper that this protocol
builds on, the constant is counted as the constant term of the last W; that is the same coefficient.

Main names:
  `hU`: the polynomial, as a function of a point. `hSl`: its value at a point as a linear form in
    the coefficients (`Spec.hide_form`). `hSumAll`: the sum over all variables. `HRounds`: "these
    are the round polynomials of this summand": earlier variables at the challenges, later ones
    summed.
  `hMu`: the sum of U; `hTr`: the round polynomials (as coefficient vectors) of Λ ψ_1 .. ψ_k + U,
    whose sum is Λ + `hMu`; both in closed form: `Spec.hide_dec` says, if every variable has
    `HVar.OK`, that they are what their names say: Λ + `hMu` is the sum, and the round polynomials,
    evaluated anywhere, are those sums (`HRounds`). (The statement holds in every commutative ring,
    so also in a polynomial ring over R, where equality of values at the indeterminate is equality
    of coefficients.)
  `HCons`: consistent messages. `hFin`: the value with which a verifier ends. `Spec.hide_cons`,
    `Spec.hide_inv_left`, `Spec.hide_inv_right`: the bijection, with its inverse `hInv` named.
    `Spec.hide_end`: the end value is the summand at γ. `Spec.hide_add`: the map is additive.
  `Spec.hide_card`: the number of consistent messages. `Spec.hide_fibre`: coefficients in R: if
    m_1 .. m_r generate M and the coefficients are ∑_u w_u m_u with w_u in R, every consistent
    tuple of messages has the same number of preimages w, and no other tuple has any.
  What zero knowledge uses. (No other file of Cb/ applies `Spec.hide_pass` or `Spec.hide_law`;
    Cb/Ld/LdPscMaskProofs.lean has a lemma of its own, `hide_law_one`.) `Spec.hide_pass`, with
    coefficients as in `Spec.hide_fibre`: for uniform coefficients and any round polynomials u that
    are consistent with a claimed sum σ, the tuple (sum of U, round polynomials of U + u) is uniform
    on the set of tuples that pass the checks for the claim "sum of U + σ". `Spec.hide_law`: so its
    law is the same for all such u.
  `Spec.hide_dec`, `Spec.hide_cons`, `Spec.hide_inv_right`, `Spec.hide_card`, `Spec.hide_fibre`,
    `Spec.hide_pass` and `Spec.hide_law` assume `HVar.OK` of every variable of the list.

Limits: this file says nothing on running times; nothing on how the coefficients are laid into the
rows of a table; no protocol. R is commutative (that paper allows any ring, with challenges from its
centre).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Prob.Linear

set_option autoImplicit false

namespace Cb
open Prob

/-- A variable of a sumcheck. -/
structure HVar (R : Type) where
  /-- the largest degree of a round polynomial -/
  n : ℕ
  /-- the "sum" over the variable: a weighted sum of values at nodes -/
  S : Type
  [finS : Fintype S]
  node : S → R
  wt : S → R
  /-- the public polynomial that fills the place of this variable in the earlier terms -/
  psi : Fin (n + 1) → R

attribute [instance] HVar.finS

section Defs
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/-- the value of a polynomial, given by its coefficients -/
def hev {n : ℕ} (c : Fin (n + 1) → M) (x : R) : M := ∑ t : Fin (n + 1), x ^ (t : ℕ) • c t

/-- the "sum" of a function, of a polynomial, of the constant 1 -/
def HVar.sum (v : HVar R) (g : R → M) : M := ∑ s, v.wt s • g (v.node s)
def HVar.phi (v : HVar R) (c : Fin (v.n + 1) → M) : M := v.sum (hev c)
def HVar.tot (v : HVar R) : R := ∑ s, v.wt s

/-- The one condition on a variable. -/
def HVar.OK (v : HVar R) : Prop := v.phi v.psi = 1

/-- the names of the coefficients; of the entries of the round polynomials; points -/
def HIdx : List (HVar R) → Type
  | [] => Unit
  | v :: l => Fin v.n ⊕ HIdx l
def RIdx : List (HVar R) → Type
  | [] => Empty
  | v :: l => Fin (v.n + 1) ⊕ RIdx l
def HPt : List (HVar R) → Type
  | [] => Unit
  | _ :: l => R × HPt l

/-- the product of the public polynomials at a point -/
def hPsi : (l : List (HVar R)) → HPt l → R
  | [], _ => 1
  | v :: l, x => hev v.psi x.1 * hPsi l x.2

/-- The hiding polynomial, as a function of a point. -/
def hU : (l : List (HVar R)) → (HIdx l → M) → HPt l → M
  | [], W, _ => W ()
  | v :: l, W, x =>
    hPsi l x.2 • hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) x.1 +
      hU l (fun i => W (.inr i)) x.2

/-- its value at a point, as a linear form in the coefficients -/
def hSl : (l : List (HVar R)) → HPt l → HIdx l → R
  | [], _, _ => 1
  | _ :: l, x, .inl t => hPsi l x.2 * x.1 ^ ((t : ℕ) + 1)
  | _ :: l, x, .inr i => hSl l x.2 i

/-- the sum over all variables -/
def hSumAll : (l : List (HVar R)) → (HPt l → M) → M
  | [], f => f ()
  | v :: l, f => v.sum fun x => hSumAll l fun xs => f (x, xs)

/-- q holds the round polynomials of the summand f at the challenges γ: everywhere, the value of a
round polynomial is f with the earlier variables at the challenges, summed over the later
variables. -/
def HRounds : (l : List (HVar R)) → (HPt l → M) → (RIdx l → M) → HPt l → Prop
  | [], _, _, _ => True
  | v :: l, f, q, γ =>
    (∀ x : R, hev (fun t : Fin (v.n + 1) => q (.inl t)) x = hSumAll l fun xs => f (x, xs)) ∧
    HRounds l (fun xs => f (γ.1, xs)) (fun i => q (.inr i)) γ.2

/-- one round polynomial: Λ ψ + (a polynomial without constant term) + a constant -/
def hRc (v : HVar R) (Λ : M) (W : Fin v.n → M) (κ : M) : Fin (v.n + 1) → M :=
  fun t => v.psi t • Λ + (Fin.cons 0 W : Fin (v.n + 1) → M) t + if t = 0 then κ else 0

/-- The sum of the hiding polynomial (`Spec.hide_dec`). -/
def hMu : (l : List (HVar R)) → (HIdx l → M) → M
  | [], W => W ()
  | v :: l, W =>
    v.phi (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) + v.tot • hMu l fun i => W (.inr i)

/-- The round polynomials of Λ ψ_1 .. ψ_k + U at the challenges γ (`Spec.hide_dec`). -/
def hTr : (l : List (HVar R)) → M → (HIdx l → M) → HPt l → RIdx l → M
  | [], _, _, _, i => i.elim
  | v :: l, Λ, W, _, .inl t => hRc v Λ (fun t => W (.inl t)) (hMu l fun i => W (.inr i)) t
  | v :: l, Λ, W, γ, .inr i =>
      hTr l (hev v.psi γ.1 • Λ + hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) γ.1)
        (fun i => W (.inr i)) γ.2 i

/-- Consistent messages for the claimed sum σ: each round polynomial sums to the value of the one
before at its challenge. -/
def HCons : (l : List (HVar R)) → M → (RIdx l → M) → HPt l → Prop
  | [], _, _, _ => True
  | v :: l, σ, q, γ =>
    v.phi (fun t => q (.inl t)) = σ ∧
    HCons l (hev (fun t => q (.inl t)) γ.1) (fun i => q (.inr i)) γ.2

/-- the value with which the verifier ends: the last round polynomial at the last challenge -/
def hFin : (l : List (HVar R)) → M → (RIdx l → M) → HPt l → M
  | [], σ, _, _ => σ
  | _ :: l, _, q, γ => hFin l (hev (fun t => q (.inl t)) γ.1) (fun i => q (.inr i)) γ.2

/-- The inverse: the coefficients, from the sum μ and the round polynomials. -/
def hInv : (l : List (HVar R)) → M → M → (RIdx l → M) → HPt l → HIdx l → M
  | [], _, μ, _, _, _ => μ
  | v :: _, Λ, _, q, _, .inl t => q (.inl t.succ) - v.psi t.succ • Λ
  | v :: l, Λ, _, q, γ, .inr i =>
      hInv l (hev v.psi γ.1 • Λ +
          hev (Fin.cons 0 fun t : Fin v.n => q (.inl t.succ) - v.psi t.succ • Λ : Fin (v.n + 1) → M)
            γ.1)
        (q (.inl 0) - v.psi 0 • Λ) (fun i => q (.inr i)) γ.2 i

/-- the plain variable: g(0) + g(1), and ψ = X -/
def HVar.plain (R : Type) [CommRing R] (n : ℕ) : HVar R :=
  ⟨n, Bool, fun b => if b then 1 else 0, fun _ => 1, fun t => if (t : ℕ) = 1 then 1 else 0⟩

/-- coefficients in R, through elements m_1 .. m_r of M -/
def hAgg {r : ℕ} (m : Fin r → M) {l : List (HVar R)} (w : HIdx l → Fin r → R) : HIdx l → M :=
  fun i => ∑ u, w i u • m u

instance HIdx.fintype : (l : List (HVar R)) → Fintype (HIdx l)
  | [] => inferInstanceAs (Fintype Unit)
  | v :: l => haveI := HIdx.fintype l; inferInstanceAs (Fintype (Fin v.n ⊕ HIdx l))
instance HIdx.decEq : (l : List (HVar R)) → DecidableEq (HIdx l)
  | [] => inferInstanceAs (DecidableEq Unit)
  | v :: l => haveI := HIdx.decEq l; inferInstanceAs (DecidableEq (Fin v.n ⊕ HIdx l))
instance RIdx.fintype : (l : List (HVar R)) → Fintype (RIdx l)
  | [] => inferInstanceAs (Fintype Empty)
  | v :: l => haveI := RIdx.fintype l; inferInstanceAs (Fintype (Fin (v.n + 1) ⊕ RIdx l))
instance RIdx.decEq : (l : List (HVar R)) → DecidableEq (RIdx l)
  | [] => inferInstanceAs (DecidableEq Empty)
  | v :: l => haveI := RIdx.decEq l; inferInstanceAs (DecidableEq (Fin (v.n + 1) ⊕ RIdx l))

end Defs

namespace Spec
section
variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

/-- States, if every variable has `HVar.OK`: the closed forms are what their names say: the sum,
and the round polynomials, of the summand Λ ψ_1 .. ψ_k + U. -/
def hide_dec : Prop :=
  ∀ l : List (HVar R), (∀ v ∈ l, v.OK) →
    ∀ (Λ : M) (W : HIdx l → M) (γ : HPt l),
      hSumAll l (fun x => hPsi l x • Λ + hU l W x) = Λ + hMu l W ∧
      HRounds l (fun x => hPsi l x • Λ + hU l W x) (hTr l Λ W γ) γ

/-- States, if every variable has `HVar.OK`: the messages are consistent. -/
def hide_cons : Prop :=
  ∀ l : List (HVar R),
    (∀ v ∈ l, v.OK) → ∀ (Λ : M) (W : HIdx l → M) (γ : HPt l), HCons l (Λ + hMu l W) (hTr l Λ W γ) γ

/-- States: the messages determine the coefficients. -/
def hide_inv_left : Prop :=
  ∀ (l : List (HVar R)) (Λ : M) (W : HIdx l → M) (γ : HPt l), hInv l Λ (hMu l W) (hTr l Λ W γ) γ = W

/-- States, if every variable has `HVar.OK`: every consistent tuple of messages is reached. -/
def hide_inv_right : Prop :=
  ∀ l : List (HVar R), (∀ v ∈ l, v.OK) →
    ∀ (Λ μ : M) (q : RIdx l → M) (γ : HPt l),
      HCons l (Λ + μ) q γ → hMu l (hInv l Λ μ q γ) = μ ∧ hTr l Λ (hInv l Λ μ q γ) γ = q

/-- The verifier ends with the value of the summand at the challenges. -/
def hide_end : Prop :=
  ∀ (l : List (HVar R)) (Λ : M) (W : HIdx l → M) (γ : HPt l),
    hFin l (Λ + hMu l W) (hTr l Λ W γ) γ = hPsi l γ • Λ + hU l W γ

/-- The value at a point is a linear form in the coefficients. -/
def hide_form : Prop :=
  ∀ (l : List (HVar R)) (W : HIdx l → M) (γ : HPt l), hU l W γ = ∑ i, hSl l γ i • W i

/-- The map from coefficients to messages is additive. -/
def hide_add : Prop :=
  ∀ (l : List (HVar R)) (Λ Λ' : M) (W W' : HIdx l → M) (γ : HPt l),
    hMu l (W + W') = hMu l W + hMu l W' ∧ hTr l (Λ + Λ') (W + W') γ = hTr l Λ W γ + hTr l Λ' W' γ

/-- The number of consistent tuples (sum, round polynomials): one free element of M for each
coefficient. (not all hypotheses are named here: see the statement below) -/
def hide_card [Fintype M] : Prop :=
  ∀ l : List (HVar R), (∀ v ∈ l, v.OK) → ∀ γ : HPt l,
    cnt (fun p : M × (RIdx l → M) => HCons l p.1 p.2 γ) = Fintype.card M ^ Fintype.card (HIdx l)

/-- States, if every variable has `HVar.OK`, for coefficients in R, through generators of M: all
consistent tuples have equally many preimages, other tuples have none. -/
def hide_fibre [Fintype R] [Fintype M] : Prop :=
  ∀ l : List (HVar R), (∀ v ∈ l, v.OK) →
    ∀ (r : ℕ) (m : Fin r → M), (∀ x : M, ∃ a : Fin r → R, ∑ u, a u • m u = x) →
      ∀ (γ : HPt l) (p : M × (RIdx l → M)),
        (HCons l p.1 p.2 γ →
          cnt (fun w : HIdx l → Fin r → R => (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ) = p) *
              Fintype.card M ^ Fintype.card (HIdx l) =
            Fintype.card R ^ (r * Fintype.card (HIdx l))) ∧
        (¬ HCons l p.1 p.2 γ →
          ∀ w : HIdx l → Fin r → R, (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ) ≠ p)

/-- Uniform on the tuples that pass the checks: u is consistent with the claimed sum σ; a tuple
(μ, q) passes if q is consistent with μ + σ.
(not all hypotheses are named here: see the statement below) -/
def hide_pass [Fintype R] [Fintype M] : Prop :=
  ∀ l : List (HVar R), (∀ v ∈ l, v.OK) →
    ∀ (r : ℕ) (m : Fin r → M), (∀ x : M, ∃ a : Fin r → R, ∑ u, a u • m u = x) →
      ∀ (γ : HPt l) (σ : M) (u : RIdx l → M), HCons l σ u γ →
        ∀ p : M × (RIdx l → M),
          (HCons l (p.1 + σ) p.2 γ →
            cnt (fun w : HIdx l → Fin r → R => (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ + u) = p) *
                Fintype.card M ^ Fintype.card (HIdx l) =
              Fintype.card R ^ (r * Fintype.card (HIdx l))) ∧
          (¬ HCons l (p.1 + σ) p.2 γ →
            ∀ w : HIdx l → Fin r → R, (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ + u) ≠ p)

/-- Under the hypotheses below, the law does not depend on u: with uniform coefficients, the sum
together with (round polynomials + u) has one law for all u consistent with one claimed sum σ. -/
def hide_law [Fintype R] [Nonempty R] : Prop :=
  ∀ l : List (HVar R), (∀ v ∈ l, v.OK) →
    ∀ (r : ℕ) (m : Fin r → M), (∀ x : M, ∃ a : Fin r → R, ∑ u, a u • m u = x) →
      ∀ (γ : HPt l) (σ : M) (u u' : RIdx l → M), HCons l σ u γ → HCons l σ u' γ →
        (unif (HIdx l → Fin r → R)).map (fun w => (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ + u)) =
          (unif (HIdx l → Fin r → R)).map (fun w => (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ + u'))

/-- The plain variable: its sum is g(0) + g(1); it meets the condition as soon as round polynomials
may have degree 1. -/
def plain_phi : Prop :=
  ∀ (n : ℕ) (c : Fin (n + 1) → M), (HVar.plain R n).phi c = hev c (0 : R) + hev c (1 : R)
def plain_psi : Prop := ∀ (n : ℕ) (x : R), 1 ≤ n → hev (HVar.plain R n).psi x = x
def plain_ok : Prop := ∀ n : ℕ, 1 ≤ n → (HVar.plain R n).OK
def plain_card : Prop :=
  ∀ k n : ℕ, Fintype.card (HIdx (List.replicate k (HVar.plain R n))) = k * n + 1

end
end Spec
end Cb
