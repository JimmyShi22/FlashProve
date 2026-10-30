-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastFactors.lean: the fast encoder's factors are the powers of the format's points,
in codes of at most 2^32 positions.

Johnson/Bind/TwinFastArrays.lean proves that the fast encoder's transform computes a polynomial's
values if its factors are the points' powers (`Factors`). This file proves that hypothesis for the
format's points (`Fmt.M1.point a`), the table of roots and the powers of 7 that the fast encoder
prepares (`rootsTable (a - 1)`, `sevens a`), for a up to 32:
   `toF_sevens`: entry k of the powers of 7 is 7^(2^k);
   `toF_rootsTable`: entry B of the table of roots is the constant of order 2^32 to the exponent
      that the bits of B give, bit j giving 2^(30 - j);
   `toF_point_pow`: the point of the position y 2^k + i, i below 2^k, to the power 2^k is 7^(2^k)
      times the constant to the exponent of y;
   `factors_point`: `Factors` holds.
The premise a ≤ 32 is used: above it the library's roots of unity stay at the order 2^32.
Limits. Nothing on bytes.

-/
import Johnson.Bind.TwinFastArrays
import Johnson.Bind.TwinFastPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open OnBytes (mulF)
open OnBytes.Slice (toF expFrom)

/-- The constant of order 2^32. (`rootW` alone is, in this namespace, the root of the committer's
hash tree, Johnson/Bind/Twin.lean.) -/
local notation "ω" => OnBytes.Slice.rootW

/-! ### Arrays -/

theorem getD_list (A : Array UInt64) (i : Nat) : A.getD i 0 = A.toList.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem getD_map_range (f : Nat → UInt64) (n k : Nat) (h : k < n) :
    ((Array.range n).map f).getD k 0 = f k := by
  have hs : k < ((Array.range n).map f).size := by
    rw [Array.size_map, Array.size_range]
    exact h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some,
    Array.getElem_map, Array.getElem_range]

theorem toF_sevens (a k : Nat) (h : k < a) : toF ((sevens a).getD k 0) = toF 7 ^ 2 ^ k := by
  unfold sevens
  rw [getD_map_range _ _ _ h, OnBytes.Slice.toF_sqN]

theorem rootsTable_succ (n : Nat) :
    rootsTable (n + 1) = rootsTable n ++ (rootsTable n).map (mulF (Fmt.M1.rootOf2 (n + 2))) := rfl

theorem size_rootsTable : ∀ n, (rootsTable n).size = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [rootsTable_succ, Array.size_append, Array.size_map, size_rootsTable n, pow_succ]
    ring

theorem getD_rootsTable_lo (n B : Nat) (h : B < 2 ^ n) :
    (rootsTable (n + 1)).getD B 0 = (rootsTable n).getD B 0 := by
  have hl : B < (rootsTable n).toList.length := by
    rw [Array.length_toList, size_rootsTable]
    exact h
  rw [getD_list, getD_list, rootsTable_succ, Array.toList_append, List.getD_append _ _ _ _ hl]

theorem getD_rootsTable_hi (n B : Nat) (h : B < 2 ^ n) :
    (rootsTable (n + 1)).getD (2 ^ n + B) 0 =
      mulF (Fmt.M1.rootOf2 (n + 2)) ((rootsTable n).getD B 0) := by
  have hlen : (rootsTable n).toList.length = 2 ^ n := by
    rw [Array.length_toList, size_rootsTable]
  have hl : B < (rootsTable n).toList.length := by
    rw [hlen]
    exact h
  have hm : B < ((rootsTable n).toList.map (mulF (Fmt.M1.rootOf2 (n + 2)))).length := by
    rw [List.length_map]
    exact hl
  rw [getD_list, getD_list, rootsTable_succ, Array.toList_append, Array.toList_map,
    List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ hm, List.getElem_map, List.getD_eq_getElem _ _ hl]

/-! ### Bits -/

theorem testBit_two_mul (B j : Nat) : (2 * B).testBit (j + 1) = B.testBit j := by
  rw [Nat.testBit_succ, Nat.mul_div_cancel_left B (by decide)]

theorem testBit_two_mul_add_one (B j : Nat) : (2 * B + 1).testBit (j + 1) = B.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  omega

theorem testBit_of_lt (B n j : Nat) (h : B < 2 ^ n) (hj : n ≤ j) : B.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hj))

/-- Where the bits that it reads are 0 the exponent is 0. -/
theorem expFrom_eq_zero (x : Nat) : ∀ (n i : Nat),
    (∀ j, i ≤ j → j < i + n → x.testBit j = false) → expFrom x n i = 0
  | 0, _, _ => rfl
  | n + 1, i, h => by
    rw [expFrom_succ, h i (Nat.le_refl i) (by omega),
      expFrom_eq_zero x n (i + 1) fun j h1 h2 => h j (by omega) (by omega)]
    rfl

/-- Of a number below 2^n no more than n bits count. -/
theorem expFrom_two_mul_more (B n m : Nat) (h : B < 2 ^ n) :
    expFrom (2 * B) (n + m) 1 = expFrom (2 * B) n 1 := by
  rw [expFrom_add, expFrom_eq_zero (2 * B) m (1 + n), Nat.add_zero]
  intro j h1 _
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [testBit_two_mul]
  exact testBit_of_lt B n j' h (by omega)

/-! ### The table of roots -/

theorem toF_rootsTable : ∀ (n B : Nat), n ≤ 31 → B < 2 ^ n →
    toF ((rootsTable n).getD B 0) = ω ^ expFrom (2 * B) n 1
  | 0, B, _, hB => by
    have h0 : B = 0 := by
      rw [pow_zero] at hB
      omega
    subst h0
    show toF 1 = ω ^ 0
    rw [OnBytes.Slice.toF_one, pow_zero]
  | n + 1, B, hn, hB => by
    have e1 : 1 + n = n + 1 := Nat.add_comm 1 n
    by_cases hlo : B < 2 ^ n
    · rw [getD_rootsTable_lo n B hlo, toF_rootsTable n B (by omega) hlo, expFrom_top, e1,
        testBit_two_mul, testBit_of_lt B n n hlo (Nat.le_refl n)]
      rfl
    · obtain ⟨B', rfl⟩ : ∃ B', B = 2 ^ n + B' := ⟨B - 2 ^ n, by omega⟩
      have hB' : B' < 2 ^ n := by
        rw [pow_succ] at hB
        omega
      have hbit : (2 ^ n + B').testBit n = true := by
        rw [Nat.testBit_two_pow_add_eq, testBit_of_lt B' n n hB' (Nat.le_refl n)]
        rfl
      have hcong : expFrom (2 * (2 ^ n + B')) n 1 = expFrom (2 * B') n 1 := by
        refine expFrom_congr _ _ n 1 fun j h1 h2 => ?_
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [testBit_two_mul, testBit_two_mul, Nat.testBit_two_pow_add_gt (by omega)]
      have e2 : 32 - (n + 1 + 1) = 32 - (n + 2) := rfl
      rw [getD_rootsTable_hi n B' hB', OnBytes.Slice.toF_mulF, OnBytes.Slice.toF_rootOf2,
        toF_rootsTable n B' (by omega) hB', expFrom_top, e1, testBit_two_mul, hbit, if_pos rfl,
        hcong, e2, pow_add, mul_comm]

/-! ### The points -/

/-- The point of the position y 2^k + i to the power 2^k. -/
theorem toF_point_pow (a k y i : Nat) (hk : k ≤ a) (ha : a ≤ 32) (hi : i < 2 ^ k) :
    toF (Fmt.M1.point a (y * 2 ^ k + i)) ^ 2 ^ k = toF 7 ^ 2 ^ k * ω ^ expFrom y (a - k) 0 := by
  have hd : (y * 2 ^ k + i) / 2 ^ k = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hi,
      Nat.zero_add]
  rw [OnBytes.Slice.toF_point, mul_pow, ← pow_mul, Nat.mul_comm (expFrom _ a 0),
    rootW_pow_shift _ a k hk ha, hd]

/-- **The fast encoder's factors are the points' powers**, in codes of at most 2^32 positions. -/
theorem factors_point (a : Nat) (ha : a ≤ 32) :
    Factors (fun x => toF (Fmt.M1.point a x)) (rootsTable (a - 1)) (sevens a) a := by
  intro k B i hi hB
  have hk : k + 1 ≤ a := by
    have h1 : 2 ^ (k + 1) ≤ 2 ^ a :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos B)) hB
    exact (Nat.pow_le_pow_iff_right (by decide)).1 h1
  obtain ⟨n, rfl⟩ : ∃ n, a = n + (k + 1) := ⟨a - (k + 1), by omega⟩
  have hBn : B < 2 ^ n := by
    rw [pow_add 2 n (k + 1)] at hB
    exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right hB (Nat.two_pow_pos (k + 1)))
  have e1 : n + (k + 1) - 1 = n + k := by omega
  have e2 : n + (k + 1) - k = n + 1 := by omega
  have htw : toF (twiddle (rootsTable (n + (k + 1) - 1)) (sevens (n + (k + 1))) k B) =
      toF 7 ^ 2 ^ k * ω ^ expFrom (2 * B) n 1 := by
    unfold twiddle
    rw [OnBytes.Slice.toF_mulF, toF_sevens _ _ (by omega), e1,
      toF_rootsTable (n + k) B (by omega)
        (Nat.lt_of_lt_of_le hBn (Nat.pow_le_pow_right (by decide) (Nat.le_add_right n k))),
      expFrom_two_mul_more B n k hBn]
  refine ⟨?_, ?_⟩
  · show toF (Fmt.M1.point _ (2 * B * 2 ^ k + i)) ^ 2 ^ k = _
    have hb : (2 * B).testBit 0 = false := by
      rw [Nat.testBit_zero]
      simp
    have e3 : (if false = true then 2 ^ (32 - (0 + 1)) else 0) + expFrom (2 * B) n (0 + 1) =
        expFrom (2 * B) n 1 := by
      rw [if_neg Bool.false_ne_true]
      exact Nat.zero_add _
    rw [toF_point_pow _ k (2 * B) i (by omega) ha hi, htw, e2, expFrom_succ, hb, e3]
  · show toF (Fmt.M1.point _ ((2 * B + 1) * 2 ^ k + i)) ^ 2 ^ k = _
    have hb : (2 * B + 1).testBit 0 = true := by
      rw [Nat.testBit_zero]
      simp
    have hc : expFrom (2 * B + 1) n (0 + 1) = expFrom (2 * B) n 1 := by
      refine expFrom_congr _ _ n 1 fun j h1 _ => ?_
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [testBit_two_mul, testBit_two_mul_add_one]
    rw [toF_point_pow _ k (2 * B + 1) i (by omega) ha hi, htw, e2, expFrom_succ, hb, if_pos rfl,
      hc, pow_add]
    show _ * (ω ^ 2 ^ 31 * _) = _
    rw [rootW_pow_half_eq]
    ring

end Bind.Twin

#print axioms Bind.Twin.getD_list
#print axioms Bind.Twin.getD_map_range
#print axioms Bind.Twin.toF_sevens
#print axioms Bind.Twin.rootsTable_succ
#print axioms Bind.Twin.size_rootsTable
#print axioms Bind.Twin.getD_rootsTable_lo
#print axioms Bind.Twin.getD_rootsTable_hi
#print axioms Bind.Twin.testBit_two_mul
#print axioms Bind.Twin.testBit_two_mul_add_one
#print axioms Bind.Twin.testBit_of_lt
#print axioms Bind.Twin.expFrom_eq_zero
#print axioms Bind.Twin.expFrom_two_mul_more
#print axioms Bind.Twin.toF_rootsTable
#print axioms Bind.Twin.toF_point_pow
#print axioms Bind.Twin.factors_point
