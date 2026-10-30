-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/SumCore.lean: the sumcheck, round by round, as algebra over a field: no text
of a verifier, no bytes, no monad. Definitions, statements and proofs.

A VARIABLE is summed by a linear functional on polynomials with d coefficients (`Wt`: the sums of 1,
X, X^2, ...; `Wt.sum`). A SUMMAND is any function S from lists of field elements (one for each
variable) to the field. `IsSum vs S c` says that S is summed by the variables vs to c, AND THAT IT
IS A POLYNOMIAL OF THE RIGHT DEGREES, in the one form that a sumcheck needs: for the first variable
there is a polynomial q of degree below d whose sum is c and whose value at every x is the sum of S
(x, ...) over the other variables.

A RUN (`Chain`): the claim c0; in each round a polynomial g of degree below d whose
sum is the running claim, and a challenge r; the next claim is g(r); the last claim is cf.

`sumcheck_rbr`: if S is summed to c, there are sets of bad challenges, each fixed by the rounds in
front and the round's polynomial, each with fewer than d members, such that every run that ends in
the summand's value at the challenges, and in which no challenge is bad, began at c.

`masked`: the same for a masked sumcheck: the run is on U + eps S + eps (t - C) Psi, where U (the
hiding polynomial) and Psi (summed to 1) are fixed before eps; it begins at mu + eps t. There is at
most one bad eps. Then C is the sum of S.

`psiProd`, `hid`: the two polynomials of the masked sumcheck's design, as functions of the
challenges, with `isSum_psiProd` and `isSum_hid`.

Nothing is said of probabilities: sets are counted.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open Polynomial

variable {K : Type} [Field K]

/-- How one variable is summed. -/
structure Wt (K : Type) [Field K] where
  /-- a polynomial in this variable has d coefficients -/
  d : ℕ
  /-- the sums of 1, X, X^2 and so on -/
  mom : ℕ → K
  /-- a polynomial whose sum is 1 (asked where it is used) -/
  psi : K[X]

/-- The sum of a polynomial. -/
def Wt.sum (w : Wt K) (q : K[X]) : K := ∑ i ∈ Finset.range w.d, w.mom i * q.coeff i

theorem Wt.sum_add (w : Wt K) (p q : K[X]) : w.sum (p + q) = w.sum p + w.sum q := by
  simp only [Wt.sum, coeff_add, mul_add, Finset.sum_add_distrib]

theorem Wt.sum_C_mul (w : Wt K) (a : K) (q : K[X]) : w.sum (C a * q) = a * w.sum q := by
  simp only [Wt.sum, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- S is summed by the variables to c, through polynomials of the variables' degrees. -/
def IsSum : List (Wt K) → (List K → K) → K → Prop
  | [], S, c => S [] = c
  | w :: vs, S, c =>
    ∃ q : K[X], q.natDegree < w.d ∧ w.sum q = c ∧ ∀ x, IsSum vs (fun rs => S (x :: rs)) (q.eval x)

theorem IsSum.add : ∀ {vs : List (Wt K)} {S T : List K → K} {c e : K},
    IsSum vs S c → IsSum vs T e → IsSum vs (fun rs => S rs + T rs) (c + e)
  | [], _, _, _, _, h, h' => by
    show _ + _ = _
    rw [show _ = _ from h, show _ = _ from h']
  | w :: vs, S, T, c, e, ⟨q, hd, hs, hq⟩, ⟨q', hd', hs', hq'⟩ =>
    ⟨q + q', lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hd hd'), by rw [Wt.sum_add, hs, hs'],
      fun x => by
        rw [eval_add]
        exact IsSum.add (hq x) (hq' x)⟩

theorem IsSum.smul (a : K) : ∀ {vs : List (Wt K)} {S : List K → K} {c : K},
    IsSum vs S c → IsSum vs (fun rs => a * S rs) (a * c)
  | [], _, _, h => by
    show a * _ = _
    rw [show _ = _ from h]
  | w :: vs, S, c, ⟨q, hd, hs, hq⟩ =>
    ⟨C a * q, lt_of_le_of_lt (natDegree_C_mul_le _ _) hd, by rw [Wt.sum_C_mul, hs],
      fun x => by
        rw [eval_mul, eval_C]
        exact IsSum.smul a (hq x)⟩

theorem IsSum.congr {vs : List (Wt K)} {S T : List K → K} {c e : K} (h : IsSum vs S c)
    (hS : ∀ rs, S rs = T rs) (hc : c = e) : IsSum vs T e := by
  have : S = T := funext hS
  subst this
  subst hc
  exact h

/-- A run: the rounds' polynomials and challenges, from the first claim to the last. -/
def Chain : List (Wt K) → List (K[X] × K) → K → K → Prop
  | [], [], c, c' => c = c'
  | w :: vs, m :: ms, c, c' => m.1.natDegree < w.d ∧ w.sum m.1 = c ∧ Chain vs ms (m.1.eval m.2) c'
  | _, _, _, _ => False

/-- No challenge of the run is bad for the rounds in front of it and its round's polynomial. -/
def NoBad [DecidableEq K] (bad : List (K[X] × K) → K[X] → Finset K) (ms : List (K[X] × K)) : Prop :=
  ∀ i m, ms[i]? = some m → m.2 ∉ bad (ms.take i) m.1

/-- The number of coefficients of the variable number i; 1 behind the last. -/
def dAt (vs : List (Wt K)) (i : ℕ) : ℕ := ((vs[i]?).map (·.d)).getD 1

/-- **The sumcheck, round by round.** -/
theorem sumcheck_rbr [DecidableEq K] : ∀ (vs : List (Wt K)) (S : List K → K) (c : K), IsSum vs S c →
    ∃ bad : List (K[X] × K) → K[X] → Finset K,
      (∀ pre g, (bad pre g).card < dAt vs pre.length) ∧
      ∀ ms c0 cf, Chain vs ms c0 cf → cf = S (ms.map (·.2)) → NoBad bad ms → c0 = c
  | [], S, c, h =>
    ⟨fun _ _ => ∅, fun _ _ => by simp [dAt], fun ms c0 cf hc hf _ => by
      cases ms with
      | nil =>
        have h1 : c0 = cf := hc
        rw [h1, hf]
        exact h
      | cons m ms => exact absurd hc (by simp [Chain])⟩
  | w :: vs, S, c, ⟨q, hd, hs, hq⟩ => by
    classical
    have ih := fun x => sumcheck_rbr vs (fun rs => S (x :: rs)) (q.eval x) (hq x)
    choose badx hcard hrun using ih
    refine ⟨fun pre g =>
      match pre with
      | [] => if g.natDegree < w.d ∧ g ≠ q then (g - q).roots.toFinset else ∅
      | m :: pre' => badx m.2 pre' g, ?_, ?_⟩
    · intro pre g
      cases pre with
      | nil =>
        have hpos : 0 < w.d := lt_of_le_of_lt (Nat.zero_le _) hd
        show (if g.natDegree < w.d ∧ g ≠ q then (g - q).roots.toFinset else ∅).card < w.d
        split
        · rename_i hg
          calc (g - q).roots.toFinset.card ≤ Multiset.card (g - q).roots :=
                Multiset.toFinset_card_le _
            _ ≤ (g - q).natDegree := card_roots' _
            _ ≤ max g.natDegree q.natDegree := natDegree_sub_le _ _
            _ < w.d := max_lt hg.1 hd
        · simpa using hpos
      | cons m pre' =>
        have := hcard m.2 pre' g
        simpa [dAt] using this
    · intro ms c0 cf hc hf hb
      cases ms with
      | nil => exact absurd hc (by simp [Chain])
      | cons m ms =>
        obtain ⟨hg, hsum, hrest⟩ := hc
        have hb' : NoBad (badx m.2) ms := fun i m' hi => by
          have := hb (i + 1) m' (by simpa using hi)
          simpa using this
        have he : m.1.eval m.2 = q.eval m.2 := hrun m.2 ms _ cf hrest (by simpa using hf) hb'
        have h0 := hb 0 m (by simp)
        by_cases hgq : m.1 = q
        · rw [← hsum, hgq, hs]
        · exfalso
          apply h0
          show m.2 ∈ (if m.1.natDegree < w.d ∧ m.1 ≠ q then (m.1 - q).roots.toFinset else ∅)
          rw [if_pos ⟨hg, hgq⟩, Multiset.mem_toFinset, mem_roots (sub_ne_zero.mpr hgq)]
          show (m.1 - q).eval m.2 = 0
          rw [eval_sub, he, sub_self]

/-! ### The masked sumcheck -/

/-- **The masked sumcheck.** U, Psi, S with their sums, mu, t and Cv are fixed first. There is at
most one bad eps; for each eps there are bad sets for the rounds. A run from mu + eps t that ends in
U + eps S + eps (t - Cv) Psi at the challenges, without a bad eps or challenge, shows Cv = sigma. -/
theorem masked [DecidableEq K] (vs : List (Wt K)) (U S Psi : List K → K) (muT sigma : K)
    (hU : IsSum vs U muT) (hS : IsSum vs S sigma) (hP : IsSum vs Psi 1) (mu t Cv : K) :
    ∃ (badE : Finset K) (bad : K → List (K[X] × K) → K[X] → Finset K),
      badE.card ≤ 1 ∧ (∀ eps pre g, (bad eps pre g).card < dAt vs pre.length) ∧
      ∀ eps ms cf, Chain vs ms (mu + eps * t) cf →
        cf = U (ms.map (·.2)) + eps * S (ms.map (·.2)) + eps * (t - Cv) * Psi (ms.map (·.2)) →
        eps ∉ badE → NoBad (bad eps) ms → Cv = sigma := by
  classical
  have hG : ∀ eps, IsSum vs (fun rs => U rs + eps * S rs + eps * (t - Cv) * Psi rs)
      (muT + eps * sigma + eps * (t - Cv) * 1) := fun eps =>
    (hU.add (hS.smul eps)).add (hP.smul (eps * (t - Cv)))
  choose bad hcard hrun using fun eps => sumcheck_rbr vs _ _ (hG eps)
  refine ⟨if Cv = sigma then ∅ else {(mu - muT) / (sigma - Cv)}, bad, ?_, hcard, ?_⟩
  · split <;> simp
  · intro eps ms cf hc hf he hb
    have h := hrun eps ms _ cf hc hf hb
    by_contra hne
    rw [if_neg hne, Finset.mem_singleton] at he
    apply he
    have hs : sigma - Cv ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [eq_div_iff hs]
    linear_combination -h

/-! ### The two polynomials of the design -/

/-- The product of the variables' psi at the challenges. -/
def psiProd : List (Wt K) → List K → K
  | [], _ => 1
  | _ :: _, [] => 0
  | w :: vs, r :: rs => psiProd vs rs * w.psi.eval r

/-- Every variable's psi has a degree below d and the sum 1. -/
def PsiOk (vs : List (Wt K)) : Prop := ∀ w ∈ vs, w.psi.natDegree < w.d ∧ w.sum w.psi = 1

theorem isSum_psiProd : ∀ (vs : List (Wt K)), PsiOk vs → IsSum vs (psiProd vs) 1
  | [], _ => rfl
  | w :: vs, h =>
    ⟨w.psi, (h w (by simp)).1, (h w (by simp)).2, fun x => by
      have ih := isSum_psiProd vs fun v hv => h v (by simp [hv])
      exact (ih.smul (w.psi.eval x)).congr (fun rs => by simp [psiProd, mul_comm]) (by ring)⟩

/-- The polynomial with the coefficients h 0, h 1, ... at X^s, X^(s + 1), ...: n of them. -/
def polyFrom (h : ℕ → K) (s n : ℕ) : K[X] := ∑ i ∈ Finset.range n, C (h i) * X ^ (s + i)

theorem natDegree_polyFrom_lt (h : ℕ → K) (s n : ℕ) (hn : 0 < s + n) :
    (polyFrom h s n).natDegree < s + n := by
  unfold polyFrom
  by_cases h0 : n = 0
  · subst h0
    simpa using hn
  · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := s + n - 1) fun i hi => ?_)
      (by omega)
    have hi' : i < n := Finset.mem_range.mp hi
    exact le_trans (natDegree_C_mul_X_pow_le _ _) (by omega)

/-- The hiding polynomial at the challenges. Its coefficients h are ordered by variable, then by
degree upwards; every variable has one for each degree from 1 up, the last one also a constant. -/
def hid : List (Wt K) → (ℕ → K) → List K → K
  | [], _, _ => 0
  | [w], h, rs => (polyFrom h 0 w.d).eval (rs.headD 0)
  | w :: v :: vs, h, rs =>
    (polyFrom h 1 (w.d - 1)).eval (rs.headD 0) * psiProd (v :: vs) rs.tail +
      hid (v :: vs) (fun i => h (w.d - 1 + i)) rs.tail

theorem isSum_hid : ∀ (vs : List (Wt K)) (h : ℕ → K), PsiOk vs → (∀ w ∈ vs, 1 ≤ w.d) →
    ∃ muT, IsSum vs (hid vs h) muT
  | [], _, _, _ => ⟨0, rfl⟩
  | [w], h, _, hd =>
    ⟨w.sum (polyFrom h 0 w.d), polyFrom h 0 w.d, by
      have := natDegree_polyFrom_lt h 0 w.d (by have := hd w (by simp); omega)
      simpa using this, rfl, fun x => rfl⟩
  | w :: v :: vs, h, hp, hd => by
    obtain ⟨m, hm⟩ := isSum_hid (v :: vs) (fun i => h (w.d - 1 + i))
      (fun u hu => hp u (by simp [hu])) (fun u hu => hd u (by simp [hu]))
    have hpsi := isSum_psiProd (v :: vs) fun u hu => hp u (by simp [hu])
    have h1 : 1 ≤ w.d := hd w (by simp)
    refine ⟨w.sum (polyFrom h 1 (w.d - 1) + C m), polyFrom h 1 (w.d - 1) + C m, ?_, rfl,
      fun x => ?_⟩
    · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ (by simpa using h1))
      have := natDegree_polyFrom_lt h 1 (w.d - 1) (by omega)
      omega
    · rw [eval_add, eval_C]
      exact ((hpsi.smul ((polyFrom h 1 (w.d - 1)).eval x)).add hm).congr
        (fun rs => by simp [hid]) (by ring)

end OnBytes.Desc.First.P1
