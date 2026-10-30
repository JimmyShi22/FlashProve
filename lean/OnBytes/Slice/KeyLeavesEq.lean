-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLeavesEq.lean: the equality vector by numbers, and the multilinear extension of a
table as a sum over numbers.

OnBytes/Slice/KeyLeaves.lean names the corners of a cube by numbers: bit t of the number belongs to
coordinate t of a point. OnBytes/Slice/KeyTreeMaps.lean has the multilinear extension of a table on
lists of 0 and 1, by recursion on the first coordinate, which is the highest variable. This file
connects the two, and has the laws of the equality vector that the statement on the leaves needs.

Main theorems.
 `sum_range_two_mul`, `sum_range_mul`   a sum over numbers, by the lowest bit, and by low and high
                                        part.
 `eqW_sum`        the equality vector adds up to 1.
 `eqW_append`     at a number with low part c and high part p it is the product of the two points'
                 vectors at c and p.
 `ext_sum`, `treeMap_sum`   the extension of a table that reads a list as a number is the sum over
                 the numbers of the equality vector times the table.
 `treeMap_leafTab`   so the map of the leaves alpha - key at a point is alpha less the sum of the
                 equality vector times the keys.
 `eqTableF_length`, `eqTableF_getD`   the written-out table of corners has the entries of the
                 equality vector.

Not claimed. Nothing on the program's functions.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeaves

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb

/-! ## Sums over numbers -/

/-- A sum over the numbers below 2 n, by the lowest bit. -/
theorem sum_range_two_mul (F : ℕ → GE) : ∀ m : ℕ,
    ∑ j ∈ Finset.range (2 * m), F j = ∑ k ∈ Finset.range m, (F (2 * k) + F (2 * k + 1))
  | 0 => rfl
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul F m, Finset.sum_range_succ, add_assoc]

/-- A sum over the numbers below a b, by low and high part. -/
theorem sum_range_mul (F : ℕ → GE) (a : ℕ) : ∀ b : ℕ,
    ∑ j ∈ Finset.range (a * b), F j =
      ∑ p ∈ Finset.range b, ∑ c ∈ Finset.range a, F (c + a * p)
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul F a b, Finset.sum_range_succ]
    refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
    rw [Nat.add_comm]

/-! ## The equality vector -/

/-- Without coordinates the equality vector is 1 at every number. -/
theorem eqW_nil (j : ℕ) : eqW [] j = 1 := rfl

/-- The first coordinate goes with the lowest bit. -/
theorem eqW_cons (x : GE) (xs : List GE) (j : ℕ) :
    eqW (x :: xs) j = (if j % 2 = 1 then x else 1 - x) * eqW xs (j / 2) := rfl

/-- The equality vector adds up to 1. -/
theorem eqW_sum : ∀ z : List GE, ∑ j ∈ Finset.range (2 ^ z.length), eqW z j = 1
  | [] => by simp [eqW]
  | x :: xs => by
    rw [List.length_cons, pow_succ', sum_range_two_mul]
    have h : ∀ k, eqW (x :: xs) (2 * k) + eqW (x :: xs) (2 * k + 1) = eqW xs k := by
      intro k
      rw [eqW_cons, eqW_cons]
      have h0 : 2 * k % 2 = 0 := by omega
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : 2 * k / 2 = k := by omega
      have h3 : (2 * k + 1) / 2 = k := by omega
      rw [h0, h1, h2, h3, if_neg (by decide), if_pos rfl]
      ring
    rw [Finset.sum_congr rfl fun k _ => h k]
    exact eqW_sum xs

/-- At the number with the low part c and the high part p. -/
theorem eqW_append : ∀ (z₁ z₂ : List GE) (c p : ℕ), c < 2 ^ z₁.length →
    eqW (z₁ ++ z₂) (c + 2 ^ z₁.length * p) = eqW z₁ c * eqW z₂ p
  | [], z₂, c, p, h => by
    have hc : c = 0 := by simpa using h
    subst hc
    simp [eqW]
  | x :: xs, z₂, c, p, h => by
    rw [List.cons_append, eqW_cons, eqW_cons, List.length_cons, pow_succ']
    rw [List.length_cons, pow_succ'] at h
    have h1 : (c + 2 * 2 ^ xs.length * p) % 2 = c % 2 := by
      rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]
    have h2 : (c + 2 * 2 ^ xs.length * p) / 2 = c / 2 + 2 ^ xs.length * p := by
      rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
    rw [h1, h2, eqW_append xs z₂ (c / 2) p (by omega), mul_assoc]

/-- One more coordinate, the highest, at a number whose highest bit is 0. -/
theorem eqW_snoc_lo (z : List GE) (x : GE) (j : ℕ) (h : j < 2 ^ z.length) :
    eqW (z ++ [x]) j = eqW z j * (1 - x) := by
  have e := eqW_append z [x] j 0 h
  rw [Nat.mul_zero, Nat.add_zero] at e
  rw [e]
  simp [eqW]

/-- The same at a number whose highest bit is 1. -/
theorem eqW_snoc_hi (z : List GE) (x : GE) (j : ℕ) (h : j < 2 ^ z.length) :
    eqW (z ++ [x]) (2 ^ z.length + j) = eqW z j * x := by
  have e := eqW_append z [x] j 1 h
  rw [Nat.mul_one, Nat.add_comm] at e
  rw [e]
  simp [eqW]

/-! ## The extension of a table, as a sum -/

/-- The element 0 is read as the bit 0. -/
theorem bitN_zero : bitN 0 = 0 := if_pos rfl

/-- The element 1 is read as the bit 1. -/
theorem bitN_one : bitN 1 = 1 := if_neg one_ne_zero

/-- The extension of a table that reads a list as a number. zs: the point, the highest variable
first. -/
theorem ext_sum (f : ℕ → GE) : ∀ (n a : ℕ) (zs : List GE), zs.length = n →
    PscF.ext n (fun q => f (numFrom a q)) zs =
      ∑ j ∈ Finset.range (2 ^ n), eqW zs.reverse j * f (a * 2 ^ n + j)
  | 0, a, zs, h => by
    have hz : zs = [] := List.length_eq_zero_iff.1 h
    subst hz
    simp [PscF.ext, numFrom, eqW]
  | n + 1, a, [], h => by cases h
  | n + 1, a, x :: zs, h => by
    have hl : zs.length = n := Nat.succ.inj h
    have hr : zs.reverse.length = n := by rw [List.length_reverse, hl]
    show (1 - x) * PscF.ext n (fun q => f (numFrom a (0 :: q))) zs +
      x * PscF.ext n (fun q => f (numFrom a (1 :: q))) zs = _
    have e0 : (fun q => f (numFrom a (0 :: q))) = fun q => f (numFrom (2 * a) q) := by
      funext q
      show f (numFrom (2 * a + bitN 0) q) = _
      rw [bitN_zero, Nat.add_zero]
    have e1 : (fun q => f (numFrom a (1 :: q))) = fun q => f (numFrom (2 * a + 1) q) := by
      funext q
      show f (numFrom (2 * a + bitN 1) q) = _
      rw [bitN_one]
    rw [e0, e1, ext_sum f n (2 * a) zs hl, ext_sum f n (2 * a + 1) zs hl, List.reverse_cons,
      pow_succ, Nat.mul_two, Finset.sum_range_add, Finset.mul_sum, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj => ?_)
      (Finset.sum_congr rfl fun j hj => ?_)
    · have hj' : j < 2 ^ zs.reverse.length := by rw [hr]; exact Finset.mem_range.1 hj
      rw [eqW_snoc_lo _ _ _ hj', show 2 * a * 2 ^ n + j = a * (2 ^ n + 2 ^ n) + j by ring]
      ring
    · have hj' : j < 2 ^ zs.reverse.length := by rw [hr]; exact Finset.mem_range.1 hj
      have e := eqW_snoc_hi zs.reverse x j hj'
      rw [hr] at e
      rw [e, show (2 * a + 1) * 2 ^ n + j = a * (2 ^ n + 2 ^ n) + (2 ^ n + j) by ring]
      ring

/-- The map of a level whose table reads a list as a number, at a point by variable. -/
theorem treeMap_sum (f : ℕ → GE) (n : ℕ) (z : List GE) (h : z.length = n) :
    treeMap n (fun q => f (numFrom 0 q)) z = ∑ j ∈ Finset.range (2 ^ n), eqW z j * f j := by
  unfold treeMap
  rw [ext_sum f n 0 z.reverse (by rw [List.length_reverse, h]), List.reverse_reverse]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.zero_mul, Nat.zero_add]

/-- The map of the leaves alpha - key at a point is alpha less the sum of the equality vector
times the keys. -/
theorem treeMap_leafTab (α : GE) (k : ℕ → GE) (n : ℕ) (z : List GE) (h : z.length = n) :
    treeMap n (leafTab α k) z = α - ∑ j ∈ Finset.range (2 ^ n), eqW z j * k j := by
  have e := treeMap_sum (fun j => α - k j) n z h
  unfold leafTab
  rw [e]
  have hs := eqW_sum z
  rw [h] at hs
  calc ∑ j ∈ Finset.range (2 ^ n), eqW z j * (α - k j)
      = (∑ j ∈ Finset.range (2 ^ n), eqW z j) * α -
          ∑ j ∈ Finset.range (2 ^ n), eqW z j * k j := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by rw [hs, one_mul]

/-! ## The written-out table of corners -/

/-- One more coordinate at the point's end: one more step of the table's loop. -/
theorem eqTableF_snoc (z : List GE) (x : GE) :
    eqTableF (z ++ [x]) =
      List.zipWith (· - ·) (eqTableF z) ((eqTableF z).map fun w => w * x) ++
        (eqTableF z).map fun w => w * x := by
  unfold eqTableF
  rw [List.foldl_append]
  rfl

/-- The written-out table has an entry for each corner. -/
theorem eqTableF_length (z : List GE) : (eqTableF z).length = 2 ^ z.length := by
  induction z using List.reverseRecOn with
  | nil => rfl
  | append_singleton z x ih =>
    rw [eqTableF_snoc, List.length_append, List.length_zipWith, List.length_map, ih, Nat.min_self,
      List.length_append, List.length_singleton, pow_succ, Nat.mul_two]

/-- The written-out table of corners has the entries of the equality vector. -/
theorem eqTableF_getD (z : List GE) : ∀ j, j < 2 ^ z.length → (eqTableF z).getD j 0 = eqW z j := by
  induction z using List.reverseRecOn with
  | nil =>
    intro j hj
    have h0 : j = 0 := by simpa using hj
    subst h0
    rfl
  | append_singleton z x ih =>
    intro j hj
    rw [List.length_append, List.length_singleton, pow_succ, Nat.mul_two] at hj
    have hl := eqTableF_length z
    rw [eqTableF_snoc]
    by_cases h : j < 2 ^ z.length
    · have hz : j <
          (List.zipWith (· - ·) (eqTableF z) ((eqTableF z).map fun w => w * x)).length := by
        rw [List.length_zipWith, List.length_map, hl, Nat.min_self]
        exact h
      rw [List.getD_append _ _ _ _ hz, List.getD_eq_getElem _ _ hz, List.getElem_zipWith,
        List.getElem_map, eqW_snoc_lo z x j h, ← ih j h,
        List.getD_eq_getElem _ _ (by rw [hl]; exact h)]
      ring
    · have hz :
          (List.zipWith (· - ·) (eqTableF z) ((eqTableF z).map fun w => w * x)).length ≤ j := by
        rw [List.length_zipWith, List.length_map, hl, Nat.min_self]
        omega
      have hj' : j - 2 ^ z.length < 2 ^ z.length := by omega
      rw [List.getD_append_right _ _ _ _ hz, List.length_zipWith, List.length_map, hl, Nat.min_self,
        List.getD_eq_getElem _ _ (by rw [List.length_map, hl]; exact hj'), List.getElem_map]
      have e := eqW_snoc_hi z x (j - 2 ^ z.length) hj'
      rw [show 2 ^ z.length + (j - 2 ^ z.length) = j by omega] at e
      rw [e, ← ih _ hj', List.getD_eq_getElem _ _ (by rw [hl]; exact hj')]

end OnBytes.Slice.Leaves
