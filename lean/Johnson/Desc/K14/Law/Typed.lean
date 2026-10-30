-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Typed.lean: the equation FoldEq, on vectors that are indexed by numbers, is the
library's typed row FoldR (Cb/Ld/LdLinWords.lean) at data made of the public shape.

Main names: bitsOf (the lowest k bits of a number as a vertex of the cube), numOf (a vertex as a
number), eqK_ofFn (eqK at a point is the library's eq at the number's bits), sum_bits (a sum over
the cube's vertices is a sum over the numbers below 2 ^ k), numOf_bitsOf, linW (the typed data on
vectors: the rows of M as Fin matrixRows; a row's bits; entry (y, j) at the place j + 2 ^ kLo y),
foldR_iff.

What is not claimed. The encoded index's typed data (its generator matrix, its sample map, its
decoder) is a letter here. Nothing on the typed rows RecRow, ColT, Dot, Eval. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Catches
import Cb.Ld.LdLinWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params

variable {K : Type} [Field K]

/-- The lowest k bits of j, as a vertex of the cube. -/
def bitsOf (k j : Nat) : Fin k → Bool := fun i => j.testBit i

/-- A vertex of the cube as a number, the first coordinate lowest. -/
def numOf : (k : Nat) → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, b => (if b 0 then 1 else 0) + 2 * numOf k (Fin.tail b)

/-- The bits of an even number, and of an odd one. -/
theorem bitsOf_even (k j : Nat) : bitsOf (k + 1) (2 * j) = Fin.cons false (bitsOf k j) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [bitsOf, Nat.testBit_zero]
  · simp [bitsOf, Nat.testBit_succ]

@[inherit_doc bitsOf_even]
theorem bitsOf_odd (k j : Nat) : bitsOf (k + 1) (2 * j + 1) = Fin.cons true (bitsOf k j) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [bitsOf, Nat.testBit_zero]
  · have : (2 * j + 1) / 2 = j := by omega
    simp [bitsOf, Nat.testBit_succ, this]

/-- eqK at a point is the library's eq at the number's bits. -/
theorem eqK_ofFn : ∀ (k : Nat) (z : Fin k → K) (j : Nat),
    eqK (List.ofFn z) j = Alg.eqk z (bitsOf k j)
  | 0, z, j => by simp [eqK, Alg.eqk]
  | k + 1, z, j => by
    rw [List.ofFn_succ, eqK, eqK_ofFn k, Alg.eqk, Alg.eqk, Fin.prod_univ_succ]
    congr 1
    · simp [bitsOf, Nat.testBit_zero]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [bitsOf, Nat.testBit_succ]

/-- A sum over the cube's vertices is a sum over the numbers below 2 ^ k. -/
theorem sum_bits : ∀ (k : Nat) (F : (Fin k → Bool) → K),
    ∑ b, F b = ∑ j ∈ Finset.range (2 ^ k), F (bitsOf k j)
  | 0, F => by
    rw [Nat.pow_zero, Finset.sum_range_one, Fintype.sum_unique]
    exact congrArg F (Subsingleton.elim _ _)
  | k + 1, F => by
    rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
      sum_bits k, sum_bits k, show 2 ^ (k + 1) = 2 * 2 ^ k by ring, sum_range_two_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bitsOf_even, bitsOf_odd, add_comm]
    rfl

/-- The number of a number's lowest bits is the number, below 2 ^ k. -/
theorem numOf_bitsOf : ∀ (k j : Nat), j < 2 ^ k → numOf k (bitsOf k j) = j
  | 0, j, h => by
    have : j = 0 := by simpa using h
    subst this; rfl
  | k + 1, j, h => by
    have ht : Fin.tail (bitsOf (k + 1) j) = bitsOf k (j / 2) := by
      funext i
      simp [Fin.tail, bitsOf, Nat.testBit_succ]
    have h2 : j / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at h
      omega
    rw [numOf, ht, numOf_bitsOf k (j / 2) h2]
    have h0 : bitsOf (k + 1) j 0 = decide (j % 2 = 1) := by simp [bitsOf, Nat.testBit_zero]
    rw [h0]
    by_cases hj : j % 2 = 1
    · simp [hj]; omega
    · simp [hj]; omega

/-- **The typed data on vectors, of the public shape.** X: the encoded index's typed data; at: the
place of a row's message with a given number. -/
def linW {ι κ J : Type} (S : LinShape) (X : Cb.LdIx K ι κ J) (at' : Nat → J) :
    Cb.LdLinW K ι κ J (Fin S.matrixRows) where
  X := X
  klo := S.kLo
  l := S.kRow
  lay := fun x => at' (numOf S.kLo x.2 + 2 ^ S.kLo * x.1.val)
  py := fun y => bitsOf S.kRow y.val

/-- **FoldEq is the typed row FoldR.** -/
theorem foldR_iff {ι κ J : Type} (S : LinShape) (X : Cb.LdIx K ι κ J) (at' : Nat → J)
    (zeta : Fin S.kRow → K) (psiLo : Fin S.kLo → K) (um : J → K) (omega : Nat → K) :
    (linW S X at').FoldR zeta psiLo um (fun y => omega y.val) ↔
      FoldEq S (List.ofFn psiLo) (List.ofFn zeta) omega (fun n => um (at' n)) := by
  unfold Cb.LdLinW.FoldR Cb.LdLinW.omU FoldEq
  have hL : ∑ y : Fin S.matrixRows, Alg.eqk zeta ((linW S X at').py y) * omega y.val =
      ∑ j ∈ Finset.range S.matrixRows, eqK (List.ofFn zeta) j * omega j := by
    rw [← Fin.sum_univ_eq_sum_range fun j => eqK (List.ofFn zeta) j * omega j]
    exact Finset.sum_congr rfl fun y _ => by rw [eqK_ofFn]; rfl
  have hRt : ∑ y : Fin S.matrixRows, Alg.eqk zeta ((linW S X at').py y) *
        ∑ j : Fin S.kLo → Bool, Alg.eqk psiLo j * um ((linW S X at').lay (y, j)) =
      ∑ j ∈ Finset.range S.matrixRows, ∑ t ∈ Finset.range (2 ^ S.kLo),
        eqK (List.ofFn psiLo) t * eqK (List.ofFn zeta) j * um (at' (t + 2 ^ S.kLo * j)) := by
    rw [← Fin.sum_univ_eq_sum_range fun j => ∑ t ∈ Finset.range (2 ^ S.kLo),
      eqK (List.ofFn psiLo) t * eqK (List.ofFn zeta) j * um (at' (t + 2 ^ S.kLo * j))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [sum_bits, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have e : (linW S X at').lay (y, bitsOf S.kLo t) = at' (t + 2 ^ S.kLo * y.val) := by
      show at' (numOf S.kLo (bitsOf S.kLo t) + 2 ^ S.kLo * y.val) = _
      rw [numOf_bitsOf _ _ (Finset.mem_range.1 ht)]
    rw [e, eqK_ofFn, eqK_ofFn]
    show Alg.eqk zeta (bitsOf S.kRow y.val) * _ = _
    ring
  exact ⟨fun h => by rw [← hL, ← hRt]; exact h, fun h => by
    have := h
    rw [← hL, ← hRt] at this
    exact this⟩

end Desc.K14.Law
