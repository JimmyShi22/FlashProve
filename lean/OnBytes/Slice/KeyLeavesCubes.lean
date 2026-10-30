-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLeavesCubes.lean: a stretch of key numbers, cut into aligned cubes.

`Lkp.cubesOf` (OnBytes/Iop/Lkp.lean) cuts a run of padding into cubes: sets of key numbers that
agree with a value on the bits of a mask. Each cube is an aligned block of numbers, the largest that
begins at the next number and fits what is left. `Lkp.cubeWeight` adds the equality vector up over a
cube, as a product over the masked bits. This file shows, for runs of padding whose places are
neighbours (logStep 0, the only kind that OnBytes/Iop/Wf.lean makes): the cubes' weights add up to
the sum of the equality vector over the run's numbers.

The loop that cuts has a bound on its number of steps, 130, and the search for a block's size has
one, 62. That the first bound is never met is not shown here. It is asked as a public test on the
run (`Covered`): a twin of the loop that returns how many numbers are left after the steps returns
0. The second bound needs nothing: whatever size the search stops at, the block is aligned and fits.

Main definitions: `cubeWI` (a cube's weight by recursion), `leftAfter`, `Covered`.
Main theorems.
 `cubeWeightF_eq`     the program's loop for a cube's weight, as a recursion.
 `cubeWI_block`       if the mask has exactly the bits from b on, the weight is the equality vector
                     of the coordinates from b on, at the value without its low b bits.
 `mask_testBit`       the mask that the loop writes has exactly the bits from b on, below the number
                     of bits.
 `block_sum`          the equality vector's sum over an aligned block.
 `growBits_spec`      the block that the search finds is aligned and fits.
 `cubesLoop_sum`, `cubesOf_sum`   the cubes' weights add up to the sum over the run's numbers.
 `sum_Ico_mul`, `stretch_sum`   the sum over the key numbers of a stretch of places is the sum of
                     the place coordinates' equality vector over the places.

Not claimed. That 130 steps are enough (OnBytes/Slice/KeyLeavesFuel.lean shows it for runs below
2 ^ 61). Nothing on runs of padding with a step other than 1.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeavesEq

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb

/-! ## A cube's weight -/

/-- A cube's weight, by recursion. s: the number of the first coordinate's bit. -/
def cubeWI (mask value : ℕ) : ℕ → List GE → GE
  | _, [] => 1
  | s, x :: xs =>
    (if mask.testBit s then pickF (value.testBit s) x else 1) * cubeWI mask value (s + 1) xs

/-- The program's loop for a cube's weight, from any variable and any running value. -/
theorem foldl_cube (mask value : ℕ) : ∀ (z : List GE) (s : ℕ) (w : GE),
    ((List.range' s z.length).zip z).foldl (fun w p =>
      if mask.testBit p.1 then w * pickF (value.testBit p.1) p.2 else w) w =
      w * cubeWI mask value s z
  | [], _, w => by simp [cubeWI]
  | x :: xs, s, w => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons,
      foldl_cube mask value xs (s + 1), cubeWI]
    by_cases h : mask.testBit s = true
    · simp only [h, if_true]
      ring
    · simp only [h, Bool.false_eq_true, if_false]
      ring

/-- The program's loop for a cube's weight, as a recursion. -/
theorem cubeWeightF_eq (c : Lkp.Cube) (z : List GE) :
    cubeWeightF c z = cubeWI c.mask c.value 0 z := by
  unfold cubeWeightF
  rw [List.range_eq_range', foldl_cube, one_mul]

/-- If the mask has, among the coordinates' bits, exactly those from b on, the weight is the
equality vector of the coordinates from b on, at the value without its low bits. -/
theorem cubeWI_block (mask value b : ℕ) : ∀ (z : List GE) (s : ℕ),
    (∀ t, s ≤ t → t < s + z.length → mask.testBit t = decide (b ≤ t)) →
    cubeWI mask value s z = eqW (z.drop (b - s)) (value / 2 ^ max b s)
  | [], _, _ => by simp [cubeWI, eqW]
  | x :: xs, s, h => by
    have ih := cubeWI_block mask value b xs (s + 1) fun t h1 h2 =>
      h t (by omega) (by rw [List.length_cons]; omega)
    have hs := h s (le_refl s) (by rw [List.length_cons]; omega)
    rw [cubeWI, ih, hs]
    by_cases hb : b ≤ s
    · have e1 : b - s = 0 := by omega
      have e2 : b - (s + 1) = 0 := by omega
      have e3 : max b s = s := by omega
      have e4 : max b (s + 1) = s + 1 := by omega
      rw [e1, e2, e3, e4, List.drop_zero, List.drop_zero, eqW_cons, decide_eq_true hb, if_pos rfl,
        Nat.div_div_eq_div_mul, ← pow_succ]
      congr 1
      unfold pickF
      rw [Nat.testBit_eq_decide_div_mod_eq]
      by_cases h1 : value / 2 ^ s % 2 = 1
      · rw [decide_eq_true h1, if_pos rfl, if_pos h1]
      · rw [decide_eq_false h1, if_neg (by decide), if_neg h1]
    · have e1 : b - s = (b - (s + 1)) + 1 := by omega
      have e3 : max b s = b := by omega
      have e4 : max b (s + 1) = b := by omega
      rw [e1, e3, e4, List.drop_succ_cons, decide_eq_false hb, if_neg (by decide), one_mul]

/-- The mask that the loop writes for a block of 2 ^ b numbers. -/
theorem mask_testBit (n b t : ℕ) (ht : t < n) :
    ((2 ^ n - 1) ^^^ ((2 ^ n - 1) &&& ((2 ^ b - 1) * 2 ^ 0))).testBit t = decide (b ≤ t) := by
  rw [pow_zero, Nat.mul_one, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_one, decide_eq_true ht]
  by_cases h : t < b
  · rw [decide_eq_true h, decide_eq_false (by omega)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]
    rfl

/-- The equality vector's sum over an aligned block of 2 ^ b numbers. -/
theorem block_sum (z : List GE) (b x : ℕ) (hb : b ≤ z.length) (hx : x % 2 ^ b = 0) :
    ∑ j ∈ Finset.Ico x (x + 2 ^ b), eqW z j = eqW (z.drop b) (x / 2 ^ b) := by
  have hk : (z.take b).length = b := by rw [List.length_take]; omega
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have e : ∀ c ∈ Finset.range (2 ^ b),
      eqW z (x + c) = eqW (z.take b) c * eqW (z.drop b) (x / 2 ^ b) := by
    intro c hc
    have ea := eqW_append (z.take b) (z.drop b) c (x / 2 ^ b) (by
      rw [hk]; exact Finset.mem_range.1 hc)
    rw [List.take_append_drop, hk] at ea
    rw [← ea]
    congr 1
    have := Nat.div_add_mod x (2 ^ b)
    omega
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
  have hs := eqW_sum (z.take b)
  rw [hk] at hs
  rw [hs, one_mul]

/-- The weight of the cube that the loop writes for an aligned block is the equality vector's sum
over the block. -/
theorem cube_block (z : List GE) (b x : ℕ) (hb : b ≤ z.length) (hx : x % 2 ^ b = 0) :
    cubeWeightF ⟨(2 ^ z.length - 1) ^^^ ((2 ^ z.length - 1) &&& ((2 ^ b - 1) * 2 ^ 0)),
        0 + x * 2 ^ 0⟩ z = ∑ j ∈ Finset.Ico x (x + 2 ^ b), eqW z j := by
  rw [block_sum z b x hb hx, cubeWeightF_eq,
    cubeWI_block _ _ b z 0 fun t _ ht => mask_testBit z.length b t (by omega)]
  simp

/-! ## The loop -/

/-- The block that the search finds is aligned and fits, if the block that it starts from does. -/
theorem growBits_spec (x left : ℕ) : ∀ (k b : ℕ), x % 2 ^ b = 0 → 2 ^ b ≤ left →
    x % 2 ^ Lkp.growBits x left k b = 0 ∧ 2 ^ Lkp.growBits x left k b ≤ left
  | 0, _, h1, h2 => ⟨h1, h2⟩
  | k + 1, b, h1, h2 => by
    unfold Lkp.growBits
    split
    · next h =>
      rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact growBits_spec x left k (b + 1) h.1 h.2
    · exact ⟨h1, h2⟩

/-- How many numbers are left after k steps of the loop that cuts. -/
def leftAfter : ℕ → ℕ → ℕ → ℕ
  | 0, _, left => left
  | k + 1, x, left =>
    if left == 0 then 0
    else leftAfter k (x + 2 ^ Lkp.growBits x left 62 0) (left - 2 ^ Lkp.growBits x left 62 0)

/-- The loop's steps are enough for the run of padding p, whose key numbers follow one another
(logStep 0): a public test. -/
def Covered (p : Lkp.Padding) : Prop := leftAfter 130 p.first p.length = 0

/-- The test can be evaluated. -/
instance decCovered (p : Lkp.Padding) : Decidable (Covered p) := inferInstanceAs (Decidable (_ = _))

/-- The cubes' weights add up to the sum over the numbers, if the steps are enough. -/
theorem cubesLoop_sum (z : List GE) : ∀ (k x left : ℕ), leftAfter k x left = 0 →
    x + left ≤ 2 ^ z.length →
    ((Lkp.cubesLoop z.length 0 0 k x left).map fun c => cubeWeightF c z).sum =
      ∑ j ∈ Finset.Ico x (x + left), eqW z j
  | 0, x, left, h, _ => by
    have h0 : left = 0 := h
    subst h0
    simp [Lkp.cubesLoop]
  | k + 1, x, left, h, hx => by
    unfold Lkp.cubesLoop
    unfold leftAfter at h
    by_cases h0 : left = 0
    · subst h0
      simp
    · have hne : (left == 0) = false := beq_false_of_ne h0
      rw [hne] at h ⊢
      simp only [Bool.false_eq_true, if_false] at h ⊢
      obtain ⟨g1, g2⟩ := growBits_spec x left 62 0 (by rw [pow_zero, Nat.mod_one])
        (by rw [pow_zero]; omega)
      have hb : Lkp.growBits x left 62 0 ≤ z.length :=
        (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (by omega)
      rw [List.map_cons, List.sum_cons, cube_block z _ x hb g1,
        cubesLoop_sum z k _ _ h (by omega),
        show x + 2 ^ Lkp.growBits x left 62 0 + (left - 2 ^ Lkp.growBits x left 62 0) = x + left by
          omega]
      exact Finset.sum_Ico_consecutive _ (Nat.le_add_right _ _) (by omega)

/-- The weights of the cubes of a run of padding add up to the equality vector's sum over the
run's numbers, for a run whose places are neighbours and for which the loop's steps are enough. -/
theorem cubesOf_sum (z : List GE) (p : Lkp.Padding) (h0 : p.logStep = 0) (hc : Covered p)
    (hx : p.first + p.length ≤ 2 ^ z.length) :
    ((Lkp.cubesOf p z.length).map fun c => cubeWeightF c z).sum =
      ∑ j ∈ Finset.Ico p.first (p.first + p.length), eqW z j := by
  unfold Lkp.cubesOf
  rw [h0, pow_zero, Nat.mod_one, Nat.div_one]
  exact cubesLoop_sum z 130 p.first p.length hc hx

/-! ## A stretch of places -/

/-- A sum over the numbers with high parts from lo to hi - 1. -/
theorem sum_Ico_mul (F : ℕ → GE) (a lo hi : ℕ) (h : lo ≤ hi) :
    ∑ j ∈ Finset.Ico (lo * a) (lo * a + (hi - lo) * a), F j =
      ∑ p ∈ Finset.Ico lo hi, ∑ c ∈ Finset.range a, F (c + a * p) := by
  have e : lo * a + (hi - lo) * a = a * hi := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' h, Nat.mul_comm]
  rw [e, Nat.mul_comm lo a, Finset.sum_Ico_eq_sub _ (Nat.mul_le_mul_left a h),
    Finset.sum_Ico_eq_sub _ h, sum_range_mul, sum_range_mul]

/-- The equality vector's sum over the key numbers of a stretch of places is the sum of the place
coordinates' equality vector over the places. -/
theorem stretch_sum (z : List GE) (kCol lo hi : ℕ) (hk : kCol ≤ z.length) (h : lo ≤ hi) :
    ∑ j ∈ Finset.Ico (lo * 2 ^ kCol) (lo * 2 ^ kCol + (hi - lo) * 2 ^ kCol), eqW z j =
      ∑ p ∈ Finset.Ico lo hi, eqW (z.drop kCol) p := by
  have hl : (z.take kCol).length = kCol := by rw [List.length_take]; omega
  rw [sum_Ico_mul _ _ _ _ h]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : ∀ c ∈ Finset.range (2 ^ kCol),
      eqW z (c + 2 ^ kCol * p) = eqW (z.take kCol) c * eqW (z.drop kCol) p := by
    intro c hc
    have ea := eqW_append (z.take kCol) (z.drop kCol) c p (by rw [hl]; exact Finset.mem_range.1 hc)
    rwa [List.take_append_drop, hl] at ea
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
  have hs := eqW_sum (z.take kCol)
  rw [hl] at hs
  rw [hs, one_mul]

end OnBytes.Slice.Leaves
