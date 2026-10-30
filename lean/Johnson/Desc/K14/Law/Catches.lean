-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Catches.lean: the count behind the constraint (fold) of the linear claim's
shared rounds.

A form that is linear in each coordinate of a point z, written on the basis eq(z, j), and that has
a coefficient other than 0, vanishes at no more than k |K| ^ (k - 1) of the |K| ^ k points z.
Main names: sum_eqK_cons, card_zeros_le, foldEq_iff, foldCatches.

What is not claimed. Nothing on how z is drawn, on the messages being fixed before it is drawn, or
on any verifier: this is a count over a finite field alone.

-/
import Johnson.Desc.K14.Law.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain

variable {K : Type} [Field K]

/-- A sum below 2 n, taken two by two. -/
theorem sum_range_two_mul (f : Nat → K) (n : Nat) :
    ∑ j ∈ Finset.range (2 * n), f j = ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- eq((x, l), .) at an even index. -/
theorem eqK_cons_even (x : K) (l : List K) (j : Nat) :
    eqK (x :: l) (2 * j) = (1 - x) * eqK l j := by
  have h1 : 2 * j % 2 = 0 := by omega
  have h2 : 2 * j / 2 = j := by omega
  simp [eqK, h1, h2]

/-- eq((x, l), .) at an odd index. -/
theorem eqK_cons_odd (x : K) (l : List K) (j : Nat) : eqK (x :: l) (2 * j + 1) = x * eqK l j := by
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [eqK, h1, h2]

/-- The first coordinate set: a form in one coordinate less. -/
theorem sum_eqK_cons (x : K) (l : List K) (k : Nat) (c : Nat → K) :
    ∑ j ∈ Finset.range (2 ^ (k + 1)), eqK (x :: l) j * c j =
      ∑ j ∈ Finset.range (2 ^ k), eqK l j * ((1 - x) * c (2 * j) + x * c (2 * j + 1)) := by
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring, sum_range_two_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eqK_cons_even, eqK_cons_odd]; ring

/-- The points at which the form with the coefficients c vanishes. -/
def zeros [Fintype K] [DecidableEq K] (k : Nat) (c : Nat → K) : Finset (Fin k → K) :=
  Finset.univ.filter fun z => ∑ j ∈ Finset.range (2 ^ k), eqK (List.ofFn z) j * c j = 0

/-- The zeros with a given first coordinate are zeros of the form in one coordinate less. -/
theorem card_zeros_fibre_le [Fintype K] [DecidableEq K] (k : Nat) (c : Nat → K) (x : K) :
    ((zeros (k + 1) c).filter fun z => z 0 = x).card ≤
      (zeros k fun j => (1 - x) * c (2 * j) + x * c (2 * j + 1)).card := by
  refine Finset.card_le_card_of_injOn Fin.tail ?_ ?_
  · intro z hz
    simp only [zeros, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hz ⊢
    obtain ⟨hz, rfl⟩ := hz
    rw [← sum_eqK_cons]
    have h : List.ofFn z = z 0 :: List.ofFn (Fin.tail z) := by rw [List.ofFn_succ]; rfl
    rw [← h]; exact hz
  · intro z hz w hw h
    simp only [zeros, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hz hw
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail w, h, hz.2, hw.2]

/-- A line a + x (b - a) with a or b other than 0 has no more than one zero. -/
theorem card_line_zeros_le [Fintype K] [DecidableEq K] (a b : K) (h : a ≠ 0 ∨ b ≠ 0) :
    (Finset.univ.filter fun x : K => (1 - x) * a + x * b = 0).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  by_contra hxy
  have h1 : (x - y) * (b - a) = 0 := by linear_combination hx - hy
  have h2 : b - a = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hxy)
  have hb : b = a := sub_eq_zero.1 h2
  have ha : a = 0 := by rw [hb] at hx; linear_combination hx
  rcases h with h | h
  · exact h ha
  · exact h (hb.trans ha)

/-- **The count.** A form with a coefficient other than 0 vanishes at few points. -/
theorem card_zeros_le [Fintype K] [DecidableEq K] : ∀ (k : Nat) (c : Nat → K),
    (∃ j < 2 ^ k, c j ≠ 0) → (zeros k c).card ≤ k * Fintype.card K ^ (k - 1) := by
  intro k
  induction k with
  | zero =>
    rintro c ⟨j, hj, hc⟩
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    have : zeros 0 c = ∅ := by
      simp [zeros, eqK, hc]
    simp [this]
  | succ k ih =>
    rintro c ⟨j, hj, hc⟩
    have hj2 : j / 2 < 2 ^ k := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    have hab : c (2 * (j / 2)) ≠ 0 ∨ c (2 * (j / 2) + 1) ≠ 0 := by
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · left
        rwa [show 2 * (j / 2) = j by omega]
      · right
        rwa [show 2 * (j / 2) + 1 = j by omega]
    have hB := card_line_zeros_le _ _ hab
    have hall : ∀ x : K, ((zeros (k + 1) c).filter fun z => z 0 = x).card ≤
        (if (1 - x) * c (2 * (j / 2)) + x * c (2 * (j / 2) + 1) = 0 then Fintype.card K ^ k else 0)
          + k * Fintype.card K ^ (k - 1) := by
      intro x
      refine (card_zeros_fibre_le k c x).trans ?_
      split_ifs with hx
      · refine le_trans ?_ (Nat.le_add_right _ _)
        refine (Finset.card_le_univ _).trans ?_
        simp
      · rw [Nat.zero_add]
        exact ih _ ⟨j / 2, hj2, hx⟩
    have hsum : (zeros (k + 1) c).card =
        ∑ x : K, ((zeros (k + 1) c).filter fun z => z 0 = x).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [hsum]
    refine (Finset.sum_le_sum fun x _ => hall x).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
    have h1 : (Finset.univ.filter fun x : K =>
        (1 - x) * c (2 * (j / 2)) + x * c (2 * (j / 2) + 1) = 0).card * Fintype.card K ^ k ≤
          Fintype.card K ^ k := by
      calc _ ≤ 1 * Fintype.card K ^ k := Nat.mul_le_mul_right _ hB
        _ = _ := Nat.one_mul _
    have h2 : Fintype.card K * (k * Fintype.card K ^ (k - 1)) ≤ k * Fintype.card K ^ k := by
      cases k with
      | zero => simp
      | succ k =>
        rw [Nat.add_sub_cancel]
        exact le_of_eq (by ring)
    calc _ ≤ Fintype.card K ^ k + k * Fintype.card K ^ k := Nat.add_le_add h1 h2
      _ = (k + 1) * Fintype.card K ^ k := by ring

/-- The difference that (fold) tests, as coefficients: 0 behind the rows of M. -/
def gap (S : LinShape) (psiLo : List K) (omega u : Nat → K) (j : Nat) : K :=
  if j < S.matrixRows then
    omega j - ∑ t ∈ Finset.range (2 ^ S.kLo), eqK psiLo t * u (t + 2 ^ S.kLo * j)
  else 0

/-- (fold) says that the form with these coefficients vanishes at z. -/
theorem foldEq_iff (S : LinShape) (psiLo z : List K) (omega u : Nat → K)
    (hR : S.matrixRows ≤ 2 ^ S.kRow) :
    FoldEq S psiLo z omega u ↔
      ∑ j ∈ Finset.range (2 ^ S.kRow), eqK z j * gap S psiLo omega u j = 0 := by
  have h : ∑ j ∈ Finset.range (2 ^ S.kRow), eqK z j * gap S psiLo omega u j =
      (∑ j ∈ Finset.range S.matrixRows, eqK z j * omega j) -
        ∑ j ∈ Finset.range S.matrixRows, ∑ t ∈ Finset.range (2 ^ S.kLo),
          eqK psiLo t * eqK z j * u (t + 2 ^ S.kLo * j) := by
    rw [← Finset.sum_subset (Finset.range_mono hR), ← Finset.sum_sub_distrib]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [gap, if_pos (Finset.mem_range.1 hj), mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by ring
    · intro j _ hj
      rw [gap, if_neg (fun h => hj (Finset.mem_range.2 h)), mul_zero]
  rw [h, sub_eq_zero]

/-- **CATCHES.** -/
theorem foldCatches [Fintype K] [DecidableEq K] : FoldCatches (K := K) := by
  rintro S psiLo omega u hR ⟨j, hj, hne⟩
  have hc : ∃ j < 2 ^ S.kRow, gap S psiLo omega u j ≠ 0 :=
    ⟨j, lt_of_lt_of_le hj hR, by rw [gap, if_pos hj]; exact sub_ne_zero.2 hne⟩
  refine le_trans (le_of_eq ?_) (card_zeros_le S.kRow _ hc)
  unfold zeros
  congr 1
  exact Finset.filter_congr fun z _ => foldEq_iff S psiLo _ omega u hR

end Desc.K14.Law
