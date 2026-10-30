-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaidBack.lean: THE WAY BACK UNDOES THE FORMAT's RULE, AND THE RULE
THE WAY BACK: of one laid block: the library's laidIn (Johnson/Desc/LaidAt.lean: where the laid
block holds the array's element (i, c)) and blockBack (Johnson/Desc/ProofFile/Honest/LaidData.lean:
which element it holds at (row, place)). Theorems on public data alone; no definition.

Main names (namespace ProofFile.Honest).
  back_of_place   laidIn b i c = some (r, j) gives blockBack b r j = some (i, c), WHERE THE LAID
      BLOCK IS AS LARGE IN THE TABLE AS IN ITS ARRAY: rowBits + placeBits = bitsI + bitsC. The
      premise is spent at one step: the row lies inside the rectangle.
  place_of_back   blockBack b r j = some (i, c) gives laidIn b i c = some (r, j): WITHOUT A PREMISE:
      blockBack's own fifth test (the number lies below the laid block's count of elements) does its
      work.
  place_iff_back   both ways.
  fits_even   the plan's own test on a laid block (Own.laidBlockFits, Johnson/Desc/Own/Req.lean)
      gives the premise.

Kin, not called: elemNo, elem_of, elem_unique (Johnson/Road/K4/K4PinsBlocks.lean) hold the same
arithmetic, for another function of the name laidIn (without "none") and for iOf and cOf
(Johnson/Desc/First/Batch/Law/Laid.lean), over the files of two other sub-protocols: to call them
would lay these beneath this light file. Here: core's lemmas on quotient and remainder.

Limits. ONE laid block. Of an array's list of laid blocks (arrayBack against laidAt: "the first that
holds it") and of a message's arrays (laidBack) nothing is proved: that wants the plan's test that
they lie apart. Tests: three #guard lines at the foot: the premise can be met; where it fails,
back_of_place's end fails too. Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.LaidData
import Johnson.Desc.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Params (LaidBlock)
open VerifiableInference.Desc (laidIn)

/-- Two digits. -/
theorem quotRest_two (a b B : Nat) (hb : b < B) : (a * B + b) / B = a ∧ (a * B + b) % B = b := by
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) hb
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hb, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

/-- Two digits lie below the product. -/
theorem two_below (a b A B : Nat) (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  have h : (a + 1) * B ≤ A * B := Nat.mul_le_mul_right _ ha
  rw [Nat.succ_mul] at h
  omega

/-- **THE WAY BACK UNDOES THE RULE**, where the laid block is as large in the table as in its
array. -/
theorem back_of_place (b : LaidBlock) (he : b.rowBits + b.placeBits = b.bitsI + b.bitsC)
    {i c r j : Nat} (h : laidIn b i c = some (r, j)) : blockBack b r j = some (i, c) := by
  unfold laidIn at h
  simp only at h
  split at h
  · rename_i hh
    obtain ⟨h1, h2, h3, h4⟩ := hh
    generalize hx : (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
      else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)) = x at h
    have hi : i - b.firstI < 2 ^ b.bitsI := by omega
    have hc : c - b.firstC < 2 ^ b.bitsC := by omega
    have hlt : x < 2 ^ (b.bitsI + b.bitsC) := by
      rw [← hx, Nat.pow_add]
      split
      · rw [Nat.mul_comm (2 ^ b.bitsI)]
        exact two_below _ _ _ _ hc hi
      · exact two_below _ _ _ _ hi hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hr, hj⟩ := h
    have hP : 0 < 2 ^ b.placeBits := Nat.two_pow_pos _
    have hm : x % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ hP
    have hd : x / 2 ^ b.placeBits < 2 ^ b.rowBits := by
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, Nat.add_comm, he]
      exact hlt
    have ex : (r - b.firstRow) * 2 ^ b.placeBits + (j - b.firstPlace) = x := by
      rw [← hr, ← hj, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.mul_comm]
      exact Nat.div_add_mod x _
    have hin : b.firstRow ≤ r ∧ r < b.firstRow + 2 ^ b.rowBits ∧ b.firstPlace ≤ j ∧
        j < b.firstPlace + 2 ^ b.placeBits := by
      generalize x / 2 ^ b.placeBits = q at hr hd
      generalize x % 2 ^ b.placeBits = m at hj hm
      omega
    unfold blockBack
    simp only [ex]
    rw [if_pos ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2, hlt⟩]
    by_cases hl : b.iIsLow = true
    · rw [if_pos hl] at hx ⊢
      obtain ⟨d1, d2⟩ := quotRest_two (c - b.firstC) (i - b.firstI) _ hi
      rw [hx] at d1 d2
      rw [d1, d2]
      congr 2 <;> omega
    · rw [if_neg hl] at hx ⊢
      obtain ⟨d1, d2⟩ := quotRest_two (i - b.firstI) (c - b.firstC) _ hc
      rw [hx] at d1 d2
      rw [d1, d2]
      congr 2 <;> omega
  · exact absurd h (by simp)

/-- **THE RULE UNDOES THE WAY BACK.** -/
theorem place_of_back (b : LaidBlock) {i c r j : Nat} (h : blockBack b r j = some (i, c)) :
    laidIn b i c = some (r, j) := by
  unfold blockBack at h
  generalize hx : (r - b.firstRow) * 2 ^ b.placeBits + (j - b.firstPlace) = x at h
  simp only at h
  split at h
  · rename_i hh
    obtain ⟨h1, h2, h3, h4, hlt⟩ := hh
    have hj : j - b.firstPlace < 2 ^ b.placeBits := by omega
    obtain ⟨e1, e2⟩ := quotRest_two (r - b.firstRow) (j - b.firstPlace) _ hj
    rw [hx] at e1 e2
    simp only [Option.some.injEq] at h
    have hI : 0 < 2 ^ b.bitsI := Nat.two_pow_pos _
    have hC : 0 < 2 ^ b.bitsC := Nat.two_pow_pos _
    unfold laidIn
    simp only
    by_cases hl : b.iIsLow = true
    · rw [if_pos hl] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, hc⟩ := h
      have m1 : x % 2 ^ b.bitsI < 2 ^ b.bitsI := Nat.mod_lt _ hI
      have m2 : x / 2 ^ b.bitsI < 2 ^ b.bitsC := by
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add]
        exact hlt
      have hin : b.firstI ≤ i ∧ i < b.firstI + 2 ^ b.bitsI ∧ b.firstC ≤ c ∧
          c < b.firstC + 2 ^ b.bitsC := by
        generalize x % 2 ^ b.bitsI = u at hi m1
        generalize x / 2 ^ b.bitsI = v at hc m2
        omega
      rw [if_pos hin]
      have ex : (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI) = x := by
        rw [← hi, ← hc, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.mul_comm]
        exact Nat.div_add_mod x _
      simp only [if_pos hl, ex, e1, e2]
      congr 2 <;> omega
    · rw [if_neg hl] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, hc⟩ := h
      have m1 : x % 2 ^ b.bitsC < 2 ^ b.bitsC := Nat.mod_lt _ hC
      have m2 : x / 2 ^ b.bitsC < 2 ^ b.bitsI := by
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add, Nat.add_comm]
        exact hlt
      have hin : b.firstI ≤ i ∧ i < b.firstI + 2 ^ b.bitsI ∧ b.firstC ≤ c ∧
          c < b.firstC + 2 ^ b.bitsC := by
        generalize x / 2 ^ b.bitsC = u at hi m2
        generalize x % 2 ^ b.bitsC = v at hc m1
        omega
      rw [if_pos hin]
      have ex : (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC) = x := by
        rw [← hi, ← hc, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.mul_comm]
        exact Nat.div_add_mod x _
      simp only [if_neg hl, ex, e1, e2]
      congr 2 <;> omega
  · exact absurd h (by simp)

/-- **BOTH WAYS.** -/
theorem place_iff_back (b : LaidBlock) (he : b.rowBits + b.placeBits = b.bitsI + b.bitsC)
    (i c r j : Nat) : laidIn b i c = some (r, j) ↔ blockBack b r j = some (i, c) :=
  ⟨back_of_place b he, place_of_back b⟩

/-- The plan's own test on a laid block gives the premise. -/
theorem fits_even {b : LaidBlock} {R P : Nat}
    (h : VerifiableInference.Desc.Own.laidBlockFits b R P = true) :
    b.rowBits + b.placeBits = b.bitsI + b.bitsC := by
  unfold VerifiableInference.Desc.Own.laidBlockFits at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1.1

/-! ### Tests -/

-- the premise can be met: a laid block of 2 x 4 elements in 2 rows of 4 places: every element goes
-- there and back
#guard (List.range 2).all fun i => (List.range 4).all fun c =>
  ((laidIn ⟨0, 0, 0, 0, 1, 2, 1, 2, true⟩ i c).bind fun p =>
    blockBack ⟨0, 0, 0, 0, 1, 2, 1, 2, true⟩ p.1 p.2) == some (i, c)
-- a negative test: the same elements in ONE row of 4 places: the premise fails, and element (0, 2)
-- is laid by the rule at a row that the way back does not know
#guard (laidIn ⟨0, 0, 0, 0, 1, 2, 0, 2, true⟩ 0 2) == some (1, 0)
#guard (blockBack ⟨0, 0, 0, 0, 1, 2, 0, 2, true⟩ 1 0) == none

end ProofFile.Honest

#print axioms ProofFile.Honest.quotRest_two
#print axioms ProofFile.Honest.two_below
#print axioms ProofFile.Honest.back_of_place
#print axioms ProofFile.Honest.place_of_back
#print axioms ProofFile.Honest.place_iff_back
#print axioms ProofFile.Honest.fits_even
