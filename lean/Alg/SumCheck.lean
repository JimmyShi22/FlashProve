-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/SumCheck.lean: the algebra of a sum-check, round by round: the true round polynomials and their
identities, the bad challenges of one round, and the formats of a round's message.

The masked sum-check, without the masks: "message" and "running claim" mean the underlying values,
without pads. Φ is the summand (g in Lean); g_i, ζ_i, δ_i (D in Lean) are the true polynomial,
challenge and degree bound of round i of n.

  `plainW`, `eqW`   the plain form; the form with an equality factor
  `lam`   Λ_i
  `roundPoly`   g_i, with the identities Λ_1(g_1) = the sum in the start claim, Λ_i(g_i) =
      g_(i-1)(ζ_(i-1)), g_n(ζ_n) = Φ(ζ)
  `RoundFormat`, `coeffFormat`, `valueFormat`   the formats
  `BadRound`, `RoundFormat.count_bad_le`   soundness: in every format of degree δ_i, if the summand
      has degree at most d j in each variable j (`hg`) and d i ≤ δ_i for the round's variable i
      (`hD`), at most δ_i bad challenges

The variables may be bound in any order; each challenge is stored at the coordinate of its variable.
K is a finite commutative domain for the counts, a field (F in Lean) for `coeffFormat` and
`valueFormat`.

Limits: this file does not prove the step over all rounds (if no challenge is bad and the end claim
is true, the start claim is true).
-/
import Alg.Mle
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Alg

open Finset Polynomial

variable {K : Type*} {ι : Type*} [DecidableEq ι]

/-! ## Summing out variables -/

section Defs

variable [CommRing K]

/-- Sums out the variable i with weights w: the result at z is w(0) g(z with 0 at i) + w(1) g(z with
1 at i). -/
def sumOut (w : Bool → K) (i : ι) (g : (ι → K) → K) : (ι → K) → K :=
  fun z => w false * g (Function.update z i 0) + w true * g (Function.update z i 1)

/-- Sums out the variables of a list, each variable v with its weights wt v. This is the true value
of the running claim when the variables in the list are still unbound and the challenges sampled so
far are stored in z. The value does not depend on z at the variables of the list
(sumOutL_update_of_mem). It is a sum over a cube only if no variable occurs twice in the list. -/
def sumOutL (wt : ι → Bool → K) : List ι → ((ι → K) → K) → (ι → K) → K
  | [], g => g
  | i :: l, g => sumOut (wt i) i (sumOutL wt l g)

/-- The weights of the plain form: 1 at 0 and 1 at 1, for every variable. -/
def plainW : ι → Bool → K := fun _ _ => 1

/-- The weights of the form with the equality factor eq(ρ, ·): 1 - ρ_v at 0 and ρ_v at 1, for the
variable v. The factors of the variables that are bound already are left out of the running
claim. -/
def eqW (ρ : ι → K) : ι → Bool → K := fun v β => if β then ρ v else 1 - ρ v

/-- Λ(q) = w(0) q(0) + w(1) q(1), the quantity that a round compares with the running claim. -/
def lam (w : Bool → K) (q : K[X]) : K := w false * q.eval 0 + w true * q.eval 1

/-- The value of sumOutL wt l g does not depend on z at the variables of the list l. -/
theorem sumOutL_update_of_mem (wt : ι → Bool → K) (g : (ι → K) → K) :
    ∀ (l : List ι) (z : ι → K) (j : ι) (t : K),
      j ∈ l → sumOutL wt l g (Function.update z j t) = sumOutL wt l g z
  | i :: l, z, j, t, hj => by
      by_cases h : j = i
      · subst h
        simp [sumOutL, sumOut]
      · have hj' : j ∈ l := by simpa [h] using hj
        simp only [sumOutL, sumOut]
        rw [Function.update_comm h, Function.update_comm h, sumOutL_update_of_mem wt g l _ j t hj',
          sumOutL_update_of_mem wt g l _ j t hj']

theorem DegLE.sumOut {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (w : Bool → K) (i : ι) :
    DegLE d (sumOut w i g) :=
  ((hg.update i 0).const_mul _).add ((hg.update i 1).const_mul _)

theorem DegLE.sumOutL {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g)
    (wt : ι → Bool → K) (l : List ι) : DegLE d (sumOutL wt l g) := by
  induction l with
  | nil => exact hg
  | cons i l ih => exact ih.sumOut _ _

/-- Summing out is additive in the function. -/
theorem sumOutL_finset_sum {J : Type*} (s : Finset J) (wt : ι → Bool → K) (g : J → (ι → K) → K) :
    ∀ (l : List ι) (z : ι → K),
      sumOutL wt l (fun x => ∑ j ∈ s, g j x) z = ∑ j ∈ s, sumOutL wt l (g j) z
  | [], _ => rfl
  | i :: l, z => by
      simp only [sumOutL, sumOut]
      rw [sumOutL_finset_sum s wt g l, sumOutL_finset_sum s wt g l, mul_sum,
        mul_sum, ← sum_add_distrib]

/-- A point that is stored in a longer tuple. The injection e maps the variables of g to coordinates
of the tuple. Summing out the coordinates e v of the tuple is summing out the variables v of g. -/
theorem sumOutL_comp {J : Type*} [DecidableEq J] (e : ι → J) (he : Function.Injective e)
    (wt : J → Bool → K) (g : (ι → K) → K) :
    ∀ (l : List ι) (z : J → K), sumOutL wt (l.map e) (fun y => g fun v => y (e v)) z =
      sumOutL (fun v => wt (e v)) l g (fun v => z (e v))
  | [], _ => rfl
  | i :: l, z => by
      have hu : ∀ t : K,
          (fun v => Function.update z (e i) t (e v)) = Function.update (fun v => z (e v)) i t := by
        intro t
        funext v
        by_cases hv : v = i
        · subst hv; simp
        · rw [Function.update_of_ne hv, Function.update_of_ne fun h => hv (he h)]
      simp only [List.map_cons, sumOutL, sumOut]
      rw [sumOutL_comp e he wt g l, sumOutL_comp e he wt g l, hu, hu]

/-! ## The true round polynomial -/

/-- The true round polynomial g_i of the round that binds the variable i, when the variables in rest
are still unbound after it and the earlier challenges are stored in z: a polynomial of degree at
most d i with g_i(X) = the sum of g over the variables in rest, with X at i. -/
def roundPoly {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K)
    (i : ι) (rest : List ι) (z : ι → K) : K[X] :=
  (hg.sumOutL wt rest z i).choose

theorem natDegree_roundPoly_le {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K)
    (i : ι) (rest : List ι) (z : ι → K) :
    (roundPoly hg wt i rest z).natDegree ≤ d i :=
  (hg.sumOutL wt rest z i).choose_spec.1

theorem eval_roundPoly {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K) (i : ι)
    (rest : List ι) (z : ι → K) (t : K) :
    (roundPoly hg wt i rest z).eval t = sumOutL wt rest g (Function.update z i t) :=
  ((hg.sumOutL wt rest z i).choose_spec.2 t).symm

/-- The true round polynomial does not depend on what is stored at the variable of its round. -/
theorem roundPoly_update_self {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K)
    (i : ι) (rest : List ι) (z : ι → K) (t : K) :
    roundPoly hg wt i rest (Function.update z i t) = roundPoly hg wt i rest z := by
  unfold roundPoly
  congr 1
  funext q
  simp

/-- Λ_i(g_i) is the true value of the running claim before round i. Before the first round this is
the sum in the start claim (sumOutL_univ). For i > 1, with the challenge of the round before stored
in z, it is g_(i-1)(ζ_(i-1)) (eval_roundPoly). -/
theorem lam_roundPoly {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K) (i : ι)
    (rest : List ι) (z : ι → K) :
    lam (wt i) (roundPoly hg wt i rest z) = sumOutL wt (i :: rest) g z := by
  unfold lam
  rw [eval_roundPoly, eval_roundPoly]
  rfl

/-- After the last round n: g_n(ζ_n) = Φ(ζ). -/
theorem eval_roundPoly_nil {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K)
    (i : ι) (z : ι → K) (t : K) :
    (roundPoly hg wt i [] z).eval t = g (Function.update z i t) :=
  eval_roundPoly hg wt i [] z t

end Defs

/-! ## The true value before the first round -/

section Closed

variable [CommRing K]

/-- The sum over the variables of a list without repetitions, written as an explicit sum. The index
T runs over the sets of variables that are set to 1. With eval_roundPoly this is an explicit formula
for g_i. -/
theorem sumOutL_eq_sum_powerset
    (wt : ι → Bool → K) (l : List ι) (hl : l.Nodup) (g : (ι → K) → K) (z : ι → K) :
    sumOutL wt l g z =
      ∑ T ∈ l.toFinset.powerset, (∏ v ∈ l.toFinset, wt v (decide (v ∈ T))) *
        g (fun v => if v ∈ l.toFinset then (if v ∈ T then 1 else 0) else z v) := by
  induction l generalizing z with
  | nil => simp [sumOutL]
  | cons i l ih =>
    have hi : i ∉ l.toFinset := by simpa using (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    rw [List.toFinset_cons, sum_powerset_insert hi]
    show wt i false * sumOutL wt l g _ + wt i true * sumOutL wt l g _ = _
    rw [ih hl', ih hl', mul_sum, mul_sum]
    congr 1
    · refine sum_congr rfl fun T hT => ?_
      have hiT : i ∉ T := fun h => hi (mem_powerset.mp hT h)
      rw [prod_insert hi, mul_assoc]
      simp only [hiT, decide_false]
      congr 2
      refine congrArg g (funext fun v => ?_)
      by_cases hv : v = i
      · subst hv; simp [hi, hiT]
      · simp [hv]
    · refine sum_congr rfl fun T hT => ?_
      rw [prod_insert hi, mul_assoc]
      simp only [mem_insert_self, decide_true]
      congr 1
      congr 1
      · refine prod_congr rfl fun v hv => ?_
        have : v ≠ i := fun h => hi (h ▸ hv)
        simp [this]
      · refine congrArg g (funext fun v => ?_)
        by_cases hv : v = i
        · subst hv; simp [hi]
        · simp [hv]

variable [Fintype ι]

/-- The true value before the first round. If the list contains every variable exactly once, the
value is the weighted sum over the whole cube, whatever the order of the list. -/
theorem sumOutL_univ (wt : ι → Bool → K) (l : List ι) (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (g : (ι → K) → K) (z : ι → K) :
    sumOutL wt l g z = ∑ b : ι → Bool, (∏ v, wt v (b v)) * g (corner b) := by
  have hu : l.toFinset = univ := by ext v; simp [hall v]
  rw [sumOutL_eq_sum_powerset wt l hl, hu, powerset_univ]
  refine sum_nbij' (fun T v => decide (v ∈ T)) (fun b => univ.filter fun v => b v = true)
    (by simp) (by simp) ?_ ?_ ?_
  · intro T _; ext v; simp
  · intro b _; funext v; simp
  · intro T _
    congr 2
    funext v
    simp [corner]

/-- The plain form, under `hl`, `hall`: the start claim is about ∑_x Φ(x). -/
theorem sumOutL_plain (l : List ι) (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (g : (ι → K) → K) (z : ι → K) :
    sumOutL plainW l g z = ∑ b : ι → Bool, g (corner b) := by
  rw [sumOutL_univ plainW l hl hall]
  simp [plainW]

/-- The form with an equality factor, under `hl`, `hall`: the start claim is about
∑_x eq(ρ, x) Φ(x). -/
theorem sumOutL_eq (ρ : ι → K) (l : List ι) (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (g : (ι → K) → K) (z : ι → K) :
    sumOutL (eqW ρ) l g z = ∑ b : ι → Bool, eqk ρ b * g (corner b) := by
  rw [sumOutL_univ (eqW ρ) l hl hall]
  rfl

/-- Under `hl`, `hall`: the true value before the first round of a plain sum-check on the product
of the multilinear extensions of two vectors A and B is ∑_b A_b B_b. -/
theorem sumOutL_plain_mul (l : List ι) (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (A B : (ι → Bool) → K) (z : ι → K) :
    sumOutL plainW l (fun x => mle A x * mle B x) z = ∑ b, A b * B b := by
  rw [sumOutL_plain l hl hall]
  simp only [mle_corner]

/-- Under `hl`, `hall`: with an equality factor, a sum-check on a function that agrees with the
vector A on the cube starts from ~A(ρ). -/
theorem sumOutL_eq_mle (ρ : ι → K) (l : List ι) (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    (g : (ι → K) → K) (z : ι → K) :
    sumOutL (eqW ρ) l g z = mle (fun b => g (corner b)) ρ :=
  sumOutL_eq ρ l hl hall g z

end Closed

/-! ## One round: the bad challenges -/

section Round

/-- The challenge r of the round that binds i is bad: the running claim c before the round is false,
and the running claim next r after it is true. The condition that no coordinate ρ_l, l ≤ i, of an
equality factor is 0 is not part of this definition. For the round's own coordinate ρ_i it is the
hypothesis w(1) ≠ 0 of the formats below, and part of the predicate that `coeffNext_count_bad_le`
counts. (With an equality factor the weights are `eqW ρ`, which are ρ_v at 1, for the variable v;
`coeffPoly` divides by w(1).) -/
def BadRound [CommRing K] (wt : ι → Bool → K) (g : (ι → K) → K) (i : ι) (rest : List ι) (z : ι → K)
    (c : K) (next : K → K) (r : K) : Prop :=
  c ≠ sumOutL wt (i :: rest) g z ∧ next r = sumOutL wt rest g (Function.update z i r)

variable [CommRing K] [IsDomain K] [Finite K]

/-- One round of a sum-check. The function g has degree at most d j in each variable j (`hg`), and
d i ≤ D for the variable i that the round binds (`hD`). The polynomial h has degree at most D; it
stands for the polynomial that the running claim and the prover's message determine, so Λ(h) is the
running claim. If the running claim differs from the true value, then the next running claim h(r)
equals the next true value for at most D values of the challenge r. -/
theorem sumcheck_round {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K) (i : ι)
    (rest : List ι) (z : ι → K) {D : ℕ} (hD : d i ≤ D) (h : K[X]) (hh : h.natDegree ≤ D)
    (hfalse : lam (wt i) h ≠ sumOutL wt (i :: rest) g z) :
    Nat.card {r : K // h.eval r = sumOutL wt rest g (Function.update z i r)} ≤ D := by
  have hne : h ≠ roundPoly hg wt i rest z := by
    rintro rfl
    exact hfalse (lam_roundPoly hg wt i rest z)
  refine le_trans (count_mono fun r hr => ?_)
    (count_eval_eq_le hne hh ((natDegree_roundPoly_le hg wt i rest z).trans hD))
  rw [hr, eval_roundPoly]

/-- Under `hg`, `hD`: at most D challenges of a round are bad, for a verifier that computes the
next running claim by a function next of the challenge. It suffices that next is the evaluation of
some polynomial h of degree at most D with Λ(h) = c. -/
theorem sumcheck_round_of_format {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (wt : ι → Bool → K)
    (i : ι) (rest : List ι) (z : ι → K) {D : ℕ} (hD : d i ≤ D) (c : K) (next : K → K)
    (hfmt : ∃ h : K[X], h.natDegree ≤ D ∧ lam (wt i) h = c ∧ ∀ r, next r = h.eval r) :
    Nat.card {r : K // BadRound wt g i rest z c next r} ≤ D := by
  obtain ⟨h, hh, hc, hn⟩ := hfmt
  by_cases hfalse : c = sumOutL wt (i :: rest) g z
  · rw [count_eq_zero fun r hr => hr.1 hfalse]
    exact Nat.zero_le _
  · refine le_trans (count_mono fun r hr => ?_)
      (sumcheck_round hg wt i rest z hD h hh (hc ▸ hfalse))
    rw [← hn]
    exact hr.2

end Round

/-! ## Formats of a round -/

section Format

/-- A format of a round of degree D with weights w. The prover sends D scalars. They and the
equation Λ(h) = c, where c is the running claim, determine a polynomial h of degree at most D, and
the next running claim h(r) is a linear form in c and the scalars whose coefficients the verifier
computes from the challenge r (and from w). -/
structure RoundFormat (K : Type*) [CommRing K] (w : Bool → K) (D : ℕ) where
  /-- the coefficient of the running claim in the next running claim -/
  cClaim : K → K
  /-- the coefficients of the scalars in the next running claim -/
  cMsg : K → Fin D → K
  /-- the scalars that describe a polynomial: what the honest prover sends -/
  scalars : K[X] → Fin D → K
  /-- whatever is sent, the next running claim is h(r) for one polynomial h of degree at most D with
  Λ(h) = c -/
  sound : ∀ (c : K) (m : Fin D → K), ∃ h : K[X], h.natDegree ≤ D ∧ lam w h = c ∧
    ∀ r, cClaim r * c + ∑ j, cMsg r j * m j = h.eval r
  /-- for every q of degree at most D: from Λ(q) and the scalars of q, the next running claim is
  q(r) -/
  complete : ∀ q : K[X],
    q.natDegree ≤ D → ∀ r, cClaim r * lam w q + ∑ j, cMsg r j * scalars q j = q.eval r

variable [CommRing K]

/-- The next running claim, from the running claim c, the scalars m and the challenge r. -/
def RoundFormat.next {w : Bool → K} {D : ℕ} (F : RoundFormat K w D) (c : K)
    (m : Fin D → K) (r : K) : K :=
  F.cClaim r * c + ∑ j, F.cMsg r j * m j

/-- The honest round, under `hg`, `hD`. If the running claim is true and the prover sends the
scalars of the true round polynomial, the next running claim is true. -/
theorem RoundFormat.next_roundPoly {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g)
    (wt : ι → Bool → K) (i : ι) (rest : List ι) (z : ι → K) {D : ℕ} (hD : d i ≤ D)
    (F : RoundFormat K (wt i) D) {c : K} (hc : c = sumOutL wt (i :: rest) g z) (r : K) :
    F.next c (F.scalars (roundPoly hg wt i rest z)) r =
      sumOutL wt rest g (Function.update z i r) := by
  rw [hc, ← lam_roundPoly hg wt i rest z, ← eval_roundPoly hg wt i rest z r]
  exact F.complete _ ((natDegree_roundPoly_le hg wt i rest z).trans hD) r

/-- Under `hg`, `hD`: at most D challenges of a round are bad, whatever the prover sends. -/
theorem RoundFormat.count_bad_le [IsDomain K] [Finite K] {d : ι → ℕ} {g : (ι → K) → K}
    (hg : DegLE d g) (wt : ι → Bool → K) (i : ι) (rest : List ι) (z : ι → K) {D : ℕ} (hD : d i ≤ D)
    (F : RoundFormat K (wt i) D) (c : K) (m : Fin D → K) :
    Nat.card {r : K // BadRound wt g i rest z c (F.next c m) r} ≤ D :=
  sumcheck_round_of_format hg wt i rest z hD c _ (F.sound c m)

end Format

/-! ## The value at 0 and the coefficients of X^2, ..., X^D -/

section Coeff

variable {F : Type*} [Field F]

/-- The polynomial a + b X + ∑_(k ≥ 2) c_k X^k with a = m 0 and c_k = m (k - 1) sent, and b solved
from Λ = c. Solving divides by w(1); with an equality factor this is the division by the coordinate
ρ_i. -/
def coeffPoly (w : Bool → F) {e : ℕ} (c : F) (m : Fin (e + 1) → F) : F[X] :=
  C (m 0) + C ((c - w false * m 0) / w true - m 0 - ∑ j : Fin e, m j.succ) * X +
    ∑ j : Fin e, C (m j.succ) * X ^ ((j : ℕ) + 2)

theorem natDegree_coeffPoly_le (w : Bool → F) {e : ℕ} (c : F) (m : Fin (e + 1) → F) :
    (coeffPoly w c m).natDegree ≤ e + 1 := by
  unfold coeffPoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · simp
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by omega))
  · exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (natDegree_C_mul_X_pow_le _ _).trans (by have := j.2; omega)

theorem eval_coeffPoly (w : Bool → F) {e : ℕ} (c : F) (m : Fin (e + 1) → F) (r : F) :
    (coeffPoly w c m).eval r =
      m 0 + ((c - w false * m 0) / w true - m 0 - ∑ j : Fin e, m j.succ) * r +
        ∑ j : Fin e, r ^ ((j : ℕ) + 2) * m j.succ := by
  unfold coeffPoly
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_finset_sum, eval_pow]
  congr 1
  exact sum_congr rfl fun j _ => mul_comm _ _

theorem lam_coeffPoly (w : Bool → F) (hw : w true ≠ 0) {e : ℕ} (c : F) (m : Fin (e + 1) → F) :
    lam w (coeffPoly w c m) = c := by
  unfold lam
  rw [eval_coeffPoly, eval_coeffPoly]
  simp only [ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, not_false_eq_true,
    zero_pow, zero_mul, sum_const_zero, mul_zero, add_zero, one_pow, one_mul, mul_one]
  generalize ∑ j : Fin e, m j.succ = S
  field_simp
  ring

private theorem sum_sub_mul {e : ℕ} (r : F) (x : Fin e → F) :
    ∑ j : Fin e, (r ^ ((j : ℕ) + 2) - r) * x j =
      (∑ j : Fin e, r ^ ((j : ℕ) + 2) * x j) - r * ∑ j : Fin e, x j := by
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- A polynomial of degree at most e + 1, written out by its coefficients. -/
private theorem eval_eq_coeffs {e : ℕ} {q : F[X]} (hq : q.natDegree ≤ e + 1) (x : F) :
    q.eval x =
      q.coeff 0 + q.coeff 1 * x + ∑ j : Fin e, x ^ ((j : ℕ) + 2) * q.coeff ((j : ℕ) + 2) := by
  rw [eval_eq_sum_range' (show q.natDegree < e + 2 by omega), sum_range_succ', sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun j => x ^ (j + 2) * q.coeff (j + 2)) e]
  have : ∑ j ∈ range e, q.coeff (j + 1 + 1) * x ^ (j + 1 + 1) =
      ∑ j ∈ range e, x ^ (j + 2) * q.coeff (j + 2) :=
    sum_congr rfl fun j _ => mul_comm _ _
  rw [this]
  simp only [zero_add, pow_zero, pow_one, mul_one]
  ring

/-- The verifier's recurrence in the format with coefficients: the next running claim from the
running claim c, the scalars m and the challenge r. It is defined for all weights; if w(1) = 0 the
division gives 0 and the value has no meaning. -/
def coeffNext (w : Bool → F) {e : ℕ} (c : F) (m : Fin (e + 1) → F) (r : F) : F :=
  r / w true * c +
    ∑ j, (Fin.cons (1 - r - r * w false / w true)
        (fun j : Fin e => r ^ ((j : ℕ) + 2) - r) : Fin (e + 1) → F) j * m j

/-- The scalars of a polynomial in the format with coefficients: the value at 0 and the coefficients
of X^2, ..., X^(e+1). -/
def coeffScalars {e : ℕ} (q : F[X]) : Fin (e + 1) → F :=
  Fin.cons (q.coeff 0) (fun j : Fin e => q.coeff ((j : ℕ) + 2))

/-- The format with coefficients, for degree e + 1 ≥ 1 and any weights with w(1) ≠ 0: the prover
sends the value at 0 and the coefficients of X^2, ..., X^(e+1); the coefficient of X is eliminated
by the round's equation. For e = 1 these are the value at 0 and the leading coefficient. (For degree
3, Basis.cubic of Alg/RoundBasis.lean chooses otherwise: the values at 0 and −1 and the coefficient
of X³.) -/
def coeffFormat (w : Bool → F) (hw : w true ≠ 0) (e : ℕ) :
    RoundFormat F w (e + 1) where
  cClaim r := r / w true
  cMsg r := Fin.cons (1 - r - r * w false / w true) (fun j : Fin e => r ^ ((j : ℕ) + 2) - r)
  scalars q := coeffScalars q
  sound c m := ⟨coeffPoly w c m, natDegree_coeffPoly_le w c m, lam_coeffPoly w hw c m, fun r => by
    rw [eval_coeffPoly, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [sum_sub_mul]
    generalize ∑ j : Fin e, r ^ ((j : ℕ) + 2) * m j.succ = S2
    generalize ∑ j : Fin e, m j.succ = S1
    field_simp
    ring⟩
  complete q hq r := by
    have h0 : q.eval 0 = q.coeff 0 := by rw [eval_eq_coeffs hq]; simp
    have h1 : q.eval 1 = q.coeff 0 + q.coeff 1 + ∑ j : Fin e, q.coeff ((j : ℕ) + 2) := by
      rw [eval_eq_coeffs hq]; simp
    unfold lam
    rw [h0, h1, eval_eq_coeffs hq r, Fin.sum_univ_succ]
    simp only [coeffScalars, Fin.cons_zero, Fin.cons_succ]
    rw [sum_sub_mul]
    generalize ∑ j : Fin e, r ^ ((j : ℕ) + 2) * q.coeff ((j : ℕ) + 2) = S2
    generalize ∑ j : Fin e, q.coeff ((j : ℕ) + 2) = S1
    field_simp
    ring

theorem coeffFormat_next (w : Bool → F) (hw : w true ≠ 0) (e : ℕ) (c : F)
    (m : Fin (e + 1) → F) (r : F) :
    (coeffFormat w hw e).next c m r = coeffNext w c m r := rfl

/-- Under `hg`, `hD`: at most e + 1 challenges of a round are bad, for the verifier's recurrence
as a total function. The condition w(1) ≠ 0 is part of the counted predicate: with an equality
factor it says that the coordinate ρ_i is not 0. Without it the bound fails. -/
theorem coeffNext_count_bad_le [Finite F] {ι : Type*} [DecidableEq ι] {d : ι → ℕ} {g : (ι → F) → F}
    (hg : DegLE d g) (wt : ι → Bool → F) (i : ι) (rest : List ι) (z : ι → F) {e : ℕ}
    (hD : d i ≤ e + 1) (c : F) (m : Fin (e + 1) → F) :
    Nat.card {r : F // wt i true ≠ 0 ∧ BadRound wt g i rest z c (coeffNext (wt i) c m) r} ≤
      e + 1 := by
  by_cases hw : wt i true = 0
  · rw [count_eq_zero fun r hr => hr.1 hw]
    exact Nat.zero_le _
  · exact le_trans (count_mono fun r hr => hr.2)
      (RoundFormat.count_bad_le hg wt i rest z hD (coeffFormat (wt i) hw e) c m)

/-- Degree 2, plain form: from the running claim c, the value q0 at 0 and the leading coefficient
q2, the next running claim is c r + q0 (1 - 2 r) + q2 (r^2 - r). -/
theorem next_plain_two (c q0 q2 r : F) :
    coeffNext (fun _ => (1 : F)) c ![q0, q2] r = c * r + q0 * (1 - 2 * r) + q2 * (r ^ 2 - r) := by
  simp [coeffNext, Fin.sum_univ_succ]
  ring

/-- Degree 2, with an equality factor whose coordinate at the variable of the round is ρ ≠ 0: the
next running claim is c (r / ρ) + q0 (1 - r / ρ) + q2 (r^2 - r). -/
theorem next_eq_two (ρ : F) (hρ : ρ ≠ 0) (c q0 q2 r : F) :
    coeffNext (fun β : Bool => if β then ρ else 1 - ρ) c ![q0, q2] r
      = c * (r / ρ) + q0 * (1 - r / ρ) + q2 * (r ^ 2 - r) := by
  simp [coeffNext, Fin.sum_univ_succ]
  field_simp
  ring

end Coeff

/-! ## A second format: the values at 0, 2, 3, ..., D -/

section Values

variable {F : Type*} [Field F]

/-- The nodes 0, 1, ..., e + 1 as elements of the field. -/
def node (e : ℕ) : Fin (e + 2) → F := fun k => ((k : ℕ) : F)

/-- The k-th Lagrange basis polynomial of the nodes 0, ..., e + 1, evaluated at r. -/
def ell (e : ℕ) (k : Fin (e + 2)) (r : F) : F :=
  (Lagrange.basis univ (node e : Fin (e + 2) → F) k).eval r

/-- The values at the nodes: m 0 at 0, the solution of the round's equation at 1, and m (k - 1) at
k ≥ 2. -/
def nodeValues (w : Bool → F) {e : ℕ} (c : F) (m : Fin (e + 1) → F) : Fin (e + 2) → F :=
  Fin.cons (m 0) (Fin.cons ((c - w false * m 0) / w true) fun j : Fin e => m j.succ)

theorem eval_interpolate_nodes {e : ℕ} (vals : Fin (e + 2) → F) (r : F) :
    (Lagrange.interpolate univ (node e : Fin (e + 2) → F) vals).eval r =
      vals 0 * ell e 0 r + vals 1 * ell e 1 r +
        ∑ j : Fin e, vals j.succ.succ * ell e j.succ.succ r := by
  rw [Lagrange.interpolate_apply, eval_finset_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [eval_mul, eval_C, ell, add_assoc]
  rfl

/-- The format that sends values, for any weights with w(1) ≠ 0: the prover sends the values at 0,
2, 3, ..., e + 1, and the value at 1 is eliminated by the round's equation. The nodes 0, ..., e + 1
must be distinct in the field, which holds if the characteristic exceeds e + 1. -/
def valueFormat (w : Bool → F) (hw : w true ≠ 0) (e : ℕ)
    (hinj : Function.Injective (node e : Fin (e + 2) → F)) : RoundFormat F w (e + 1) where
  cClaim r := ell e 1 r / w true
  cMsg r :=
    Fin.cons (ell e 0 r - ell e 1 r * w false / w true) (fun j : Fin e => ell e j.succ.succ r)
  scalars q := Fin.cons (q.eval 0) (fun j : Fin e => q.eval (node e j.succ.succ))
  sound c m := by
    have hI : Set.InjOn (node e : Fin (e + 2) → F) (univ : Finset (Fin (e + 2))) := hinj.injOn
    refine ⟨Lagrange.interpolate univ (node e) (nodeValues w c m), ?_, ?_, fun r => ?_⟩
    · have := Lagrange.degree_interpolate_le (nodeValues w c m) hI
      rw [card_univ, Fintype.card_fin] at this
      exact natDegree_le_of_degree_le this
    · have h0 := Lagrange.eval_interpolate_at_node (nodeValues w c m) hI (mem_univ 0)
      have h1 := Lagrange.eval_interpolate_at_node (nodeValues w c m) hI (mem_univ 1)
      have n0 : (node e (0 : Fin (e + 2)) : F) = 0 := by simp [node]
      have n1 : (node e (1 : Fin (e + 2)) : F) = 1 := by simp [node]
      rw [n0] at h0
      rw [n1] at h1
      unfold lam
      rw [h0, h1]
      have v0 : nodeValues w c m 0 = m 0 := rfl
      have v1 : nodeValues w c m 1 = (c - w false * m 0) / w true := rfl
      rw [v0, v1]
      field_simp
      ring
    · rw [eval_interpolate_nodes, Fin.sum_univ_succ]
      have v0 : nodeValues w c m 0 = m 0 := rfl
      have v1 : nodeValues w c m 1 = (c - w false * m 0) / w true := rfl
      have v2 : ∀ j : Fin e, nodeValues w c m j.succ.succ = m j.succ := fun _ => rfl
      simp only [v0, v1, v2, Fin.cons_zero, Fin.cons_succ]
      have : ∑ j : Fin e, ell e j.succ.succ r * m j.succ =
          ∑ j : Fin e, m j.succ * ell e j.succ.succ r :=
        sum_congr rfl fun j _ => mul_comm _ _
      rw [this]
      generalize ∑ j : Fin e, m j.succ * ell e j.succ.succ r = S
      field_simp
      ring
  complete q hq r := by
    have hI : Set.InjOn (node e : Fin (e + 2) → F) (univ : Finset (Fin (e + 2))) := hinj.injOn
    have hdeg : q.degree < ((univ : Finset (Fin (e + 2))).card : ℕ) := by
      rw [card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hq)
    have hq' := Lagrange.eq_interpolate hI hdeg
    have n0 : (node e (0 : Fin (e + 2)) : F) = 0 := by simp [node]
    have n1 : (node e (1 : Fin (e + 2)) : F) = 1 := by simp [node]
    have hr : q.eval r = q.eval 0 * ell e 0 r + q.eval 1 * ell e 1 r
        + ∑ j : Fin e, q.eval (node e j.succ.succ) * ell e j.succ.succ r := by
      conv_lhs => rw [hq']
      rw [eval_interpolate_nodes, n0, n1]
    rw [hr, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have : ∑ j : Fin e, ell e j.succ.succ r * q.eval (node e j.succ.succ) =
        ∑ j : Fin e, q.eval (node e j.succ.succ) * ell e j.succ.succ r :=
      sum_congr rfl fun j _ => mul_comm _ _
    rw [this]
    generalize ∑ j : Fin e, q.eval (node e j.succ.succ) * ell e j.succ.succ r = S
    unfold lam
    field_simp
    ring

end Values

end Alg
