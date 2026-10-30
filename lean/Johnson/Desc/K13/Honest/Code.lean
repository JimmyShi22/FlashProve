--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Code.lean: for the law of the masked sumcheck's honest scalars
(Johnson/Desc/K13/Honest/SumLaw.lean): the functions in which the law is stated, and the two
identities of a round at tables. Over any commutative ring. Definitions, and statements with their
proofs. The sumcheck, the order of the hiding polynomial's coefficients and what is sent are told in
the head of Johnson/Desc/K13/Honest/Moves.lean.
Main names:
  `dotT A B`, `dotAll S`: the sum of the products of two tables; over the rows.
  `foldsAll gs S`: the tables with all variables set.
  `uAt u n i pre gs`: the value at the challenges of: pre times all variables, plus U's part.
  `after l gs R`: a running claim behind the rounds, as the verifier makes it: each linear
    coefficient is made from the claim before. `after_cons`: one round of it.
  `dot_quad`, `dot_fold`, `dotAll_quad`, `dotAll_fold`: the two identities of a round.
  `Even2`, `Sized`, `foldT_length`, `Sized.even`, `Sized.fold`: the tables' sizes.

What is not claimed. That the verifier's text computes `after` and that its hiding form is `uAt`:
Johnson/Desc/K13/Honest/CodeRow.lean. That `eqT` is the equality vector and that tables fold to
multilinear extensions: Johnson/Desc/K13/Honest/Tables.lean. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Moves
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest

variable {K : Type} [CommRing K]

/-! ## Tables -/

/-- The sum of the products, entry by entry. -/
def dotT : List K → List K → K
  | a :: A, b :: B => a * b + dotT A B
  | _, _ => 0

/-- The sum of the products, over the rows. -/
def dotAll : List (List K × List K) → K
  | [] => 0
  | p :: S => dotT p.1 p.2 + dotAll S

/-- The rows' tables with all variables set, the first challenge first. -/
def foldsAll : List K → List (List K × List K) → List (List K × List K)
  | [], S => S
  | g :: gs, S => foldsAll gs (foldAll g S)

/-! ## The hiding polynomial at the challenges -/

/-- The value at the challenges of: pre times all variables, plus the part of U in n variables. -/
def uAt (u : ℕ → K) : ℕ → ℕ → K → List K → K
  | 0, _, pre, _ => pre
  | 1, i, pre, gs => pre * gs.headD 0 + u i + u (i + 1) * gs.headD 0 + u (i + 2) * gs.headD 0 ^ 2
  | n + 2, i, pre, gs =>
    uAt u (n + 1) (i + 2) (pre * gs.headD 0 + u i * gs.headD 0 + u (i + 1) * gs.headD 0 ^ 2) gs.tail

/-! ## What the verifier makes of what is sent -/

/-- A running claim behind the rounds, as the verifier makes it (the tie to its text:
Johnson/Desc/K13/Honest/CodeRow.lean). In each round the linear coefficient is made from the claim
before: the polynomial's values at 0 and 1 add up to that claim. -/
def after : List (K × K) → List K → K → K
  | q :: l, gs, R =>
    after l gs.tail (q.1 + (R - 2 * q.1 - q.2) * gs.headD 0 + q.2 * gs.headD 0 ^ 2)
  | [], _, R => R

/-- One round of it. -/
theorem after_cons (q : K × K) (l : List (K × K)) (g : K) (gs : List K) (R : K) :
    after (q :: l) (g :: gs) R = after l gs (q.1 + (R - 2 * q.1 - q.2) * g + q.2 * g ^ 2) := rfl

/-! ## The identities of a round -/

/-- Both tables of each row have 2 m entries, for one m. -/
def Even2 {K : Type} (S : List (List K × List K)) (m : ℕ) : Prop :=
  ∀ p ∈ S, p.1.length = 2 * m ∧ p.2.length = 2 * m

/-- The sum of the products is the round's polynomial at 0 plus at 1. -/
theorem dot_quad : ∀ (m : ℕ) (A B : List K), A.length = 2 * m → B.length = 2 * m →
    dotT A B = 2 * (quadT A B).1 + (quadT A B).2.1 + (quadT A B).2.2
  | 0, [], [], _, _ => by
    show (0 : K) = 2 * 0 + 0 + 0
    ring
  | m + 1, a0 :: a1 :: A, b0 :: b1 :: B, hA, hB => by
    have ih := dot_quad m A B (by simp only [List.length_cons] at hA; omega)
      (by simp only [List.length_cons] at hB; omega)
    show a0 * b0 + (a1 * b1 + dotT A B) =
      2 * (a0 * b0 + (quadT A B).1) + (a0 * (b1 - b0) + (a1 - a0) * b0 + (quadT A B).2.1) +
        ((a1 - a0) * (b1 - b0) + (quadT A B).2.2)
    rw [ih]
    ring
  | 0, _ :: _, _, hA, _ => by simp only [List.length_cons] at hA; omega
  | 0, [], _ :: _, _, hB => by simp only [List.length_cons] at hB; omega
  | _ + 1, [], _, hA, _ => by simp only [List.length_nil] at hA; omega
  | _ + 1, [_], _, hA, _ => by simp only [List.length_cons, List.length_nil] at hA; omega
  | _ + 1, _ :: _ :: _, [], _, hB => by simp only [List.length_nil] at hB; omega
  | _ + 1, _ :: _ :: _, [_], _, hB => by
    simp only [List.length_cons, List.length_nil] at hB; omega

/-- With the first variable set to g it is the round's polynomial at g. -/
theorem dot_fold (g : K) : ∀ (A B : List K),
    dotT (foldT g A) (foldT g B) = (quadT A B).1 + (quadT A B).2.1 * g + (quadT A B).2.2 * g ^ 2
  | a0 :: a1 :: A, b0 :: b1 :: B => by
    show (a0 + g * (a1 - a0)) * (b0 + g * (b1 - b0)) + dotT (foldT g A) (foldT g B) =
      (a0 * b0 + (quadT A B).1) + (a0 * (b1 - b0) + (a1 - a0) * b0 + (quadT A B).2.1) * g +
        ((a1 - a0) * (b1 - b0) + (quadT A B).2.2) * g ^ 2
    rw [dot_fold g A B]
    ring
  | [], _ => by
    show (0 : K) = 0 + 0 * g + 0 * g ^ 2
    ring
  | [_], _ => by
    show (0 : K) = 0 + 0 * g + 0 * g ^ 2
    ring
  | _ :: _ :: _, [] => by
    show (0 : K) = 0 + 0 * g + 0 * g ^ 2
    ring
  | _ :: _ :: _, [_] => by
    show (0 : K) = 0 + 0 * g + 0 * g ^ 2
    ring

/-- A folded table has half the entries. -/
theorem foldT_length (g : K) : ∀ (m : ℕ) (A : List K), A.length = 2 * m → (foldT g A).length = m
  | 0, [], _ => rfl
  | m + 1, _ :: _ :: A, h => by
    show (foldT g A).length + 1 = m + 1
    rw [foldT_length g m A (by simp only [List.length_cons] at h; omega)]
  | 0, _ :: _, h => by simp only [List.length_cons] at h; omega
  | _ + 1, [], h => by simp only [List.length_nil] at h; omega
  | _ + 1, [_], h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- The first identity, over the rows. -/
theorem dotAll_quad (m : ℕ) : ∀ S : List (List K × List K), Even2 S m →
    dotAll S = 2 * (quadAll S).1 + (quadAll S).2.1 + (quadAll S).2.2
  | [], _ => by
    show (0 : K) = 2 * 0 + 0 + 0
    ring
  | p :: S, h => by
    have h1 := dot_quad m p.1 p.2 (h p List.mem_cons_self).1 (h p List.mem_cons_self).2
    have h2 := dotAll_quad m S fun q hq => h q (List.mem_cons_of_mem _ hq)
    show dotT p.1 p.2 + dotAll S =
      2 * ((quadT p.1 p.2).1 + (quadAll S).1) + ((quadT p.1 p.2).2.1 + (quadAll S).2.1) +
        ((quadT p.1 p.2).2.2 + (quadAll S).2.2)
    rw [h1, h2]
    ring

/-- The second identity, over the rows. -/
theorem dotAll_fold (g : K) : ∀ S : List (List K × List K),
    dotAll (foldAll g S) = (quadAll S).1 + (quadAll S).2.1 * g + (quadAll S).2.2 * g ^ 2
  | [] => by
    show (0 : K) = 0 + 0 * g + 0 * g ^ 2
    ring
  | p :: S => by
    show dotT (foldT g p.1) (foldT g p.2) + dotAll (foldAll g S) =
      ((quadT p.1 p.2).1 + (quadAll S).1) + ((quadT p.1 p.2).2.1 + (quadAll S).2.1) * g +
        ((quadT p.1 p.2).2.2 + (quadAll S).2.2) * g ^ 2
    rw [dot_fold, dotAll_fold g S]
    ring

/-- Every table of every row has 2^n entries. -/
def Sized {K : Type} (S : List (List K × List K)) (n : ℕ) : Prop :=
  ∀ p ∈ S, p.1.length = 2 ^ n ∧ p.2.length = 2 ^ n

/-- Tables of 2^(n + 1) entries have an even number of them. -/
theorem Sized.even {K : Type} {S : List (List K × List K)} {n : ℕ} (h : Sized S (n + 1)) :
    Even2 S (2 ^ n) :=
  fun p hp => ⟨by rw [(h p hp).1]; ring, by rw [(h p hp).2]; ring⟩

/-- With the first variable set, the tables have half the entries. -/
theorem Sized.fold {S : List (List K × List K)} {n : ℕ} (h : Sized S (n + 1)) (g : K) :
    Sized (foldAll g S) n := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact ⟨foldT_length g _ _ (h.even p hp).1, foldT_length g _ _ (h.even p hp).2⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.after_cons
#print axioms VerifiableInference.Desc.K13.Honest.dot_quad
#print axioms VerifiableInference.Desc.K13.Honest.dot_fold
#print axioms VerifiableInference.Desc.K13.Honest.foldT_length
#print axioms VerifiableInference.Desc.K13.Honest.dotAll_quad
#print axioms VerifiableInference.Desc.K13.Honest.dotAll_fold
#print axioms VerifiableInference.Desc.K13.Honest.Sized.even
#print axioms VerifiableInference.Desc.K13.Honest.Sized.fold
