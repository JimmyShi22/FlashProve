-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules5Laws.lean: the test of the proof of work in words is the test in bits (for at most 64 bits
of work).

The format page (docs/format/FORMAT.md, which comes with the programs; not the edition that ships)
states the test of work on a
word: the low w bits of the first word of the test block are 0. A verifier that is stated on strings
of bits tests: the first w bits of the block are 0. With the order of bits of `Fmt.bitAt` (bit i of
a string is bit i mod 8, counted from the lowest, of byte i div 8) the two are one test for w ≤ 64.
No Mathlib.

1. What the file contains. Theorems on the definitions of Fmt/Rules1.lean and Fmt/Rules5.lean.

2. What is checked when the file compiles. Only the proofs.

3. Theorems.
   `wordAt_testBit`, `passes_bits`.
   `passes_64`: at w = 64 the test says: the whole first word is 0 (R5.5, at editions of the page
   other than the one that ships).



4. What is not claimed. Nothing for w > 64 (such a round is refused: `Fmt.askOK`).

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules5

namespace Fmt

theorem byte_testBit_high (x : UInt8) (k : Nat) (hk : 8 ≤ k) : x.toNat.testBit k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) hk))

/-- bit r of a byte, by shifting and masking -/
theorem byte_bit (x : UInt8) (r : Nat) (hr : r < 8) :
    ((x >>> (UInt8.ofNat r)) &&& 1 == 1) = x.toNat.testBit r := by
  have h1 : ((x >>> (UInt8.ofNat r)) &&& 1).toNat = (x.toNat >>> r) % 2 := by
    rw [UInt8.toNat_and, UInt8.toNat_shiftRight]
    have : (UInt8.ofNat r).toNat % 8 = r := by
      rw [UInt8.toNat_ofNat']
      omega
    rw [this]
    show (x.toNat >>> r) &&& 1 = _
    exact Nat.and_one_is_mod _
  rw [Nat.testBit, Nat.and_comm, Nat.and_one_is_mod] 
  by_cases h2 : (x.toNat >>> r) % 2 = 1
  · have : (x >>> (UInt8.ofNat r)) &&& 1 = 1 := UInt8.toNat_inj.mp (by rw [h1, h2]; rfl)
    simp [this, h2]
  · have h3 : (x.toNat >>> r) % 2 = 0 := by omega
    have : (x >>> (UInt8.ofNat r)) &&& 1 ≠ 1 := fun e => by
      have := congrArg UInt8.toNat e
      rw [h1, h3] at this
      exact absurd this (by decide)
    simp [this, h3]

/-- a bit of a byte that was moved up by s places -/
theorem sh_testBit (x : UInt8) (s : UInt64) (hs : s.toNat < 64) (k : Nat) (hk : k < 64) :
    ((x.toUInt64 <<< s).toNat).testBit k =
      (decide (s.toNat ≤ k) && x.toNat.testBit (k - s.toNat)) := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, UInt8.toNat_toUInt64]
  simp [hk]

/-- of the eight bytes only byte k div 8 has a say on bit k -/
theorem pick (x : UInt8) (j k : Nat) :
    (decide (8 * j ≤ k) && x.toNat.testBit (k - 8 * j)) =
      (decide (k / 8 = j) && x.toNat.testBit (k % 8)) := by
  by_cases h : k / 8 = j
  · have h1 : 8 * j ≤ k := by omega
    have h2 : k - 8 * j = k % 8 := by omega
    simp [h, h1, h2]
  · by_cases h1 : 8 * j ≤ k
    · have h2 : 8 ≤ k - 8 * j := by omega
      simp [h, byte_testBit_high x _ h2]
    · simp [h, h1]

/-- For k < 64, bit k of the first word is bit k of the string. -/
theorem wordAt_testBit (b : ByteArray) (k : Nat) (hk : k < 64) :
    (wordAt b 0).toNat.testBit k = bitAt b k := by
  have e0 : ((byteAt b 0).toUInt64.toNat).testBit k =
      (decide (k / 8 = 0) && (byteAt b 0).toNat.testBit (k % 8)) := by
    rw [UInt8.toNat_toUInt64, ← pick]
    simp
  have e (j : Nat) (s : UInt64) (hs : s.toNat = 8 * j) (hj : j < 8) : (((byteAt b (0 + j)).toUInt64
        <<< s).toNat).testBit k =
      (decide (k / 8 = j) && (byteAt b j).toNat.testBit (k % 8)) := by
    rw [sh_testBit _ s (by omega) k hk, hs, pick, Nat.zero_add]
  unfold wordAt bitAt
  rw [byte_bit _ _ (Nat.mod_lt _ (by decide))]
  simp only [UInt64.toNat_or, Nat.testBit_or]
  rw [e0, e 1 8 rfl (by decide), e 2 16 rfl (by decide), e 3 24 rfl (by decide),
    e 4 32 rfl (by decide), e 5 40 rfl (by decide), e 6 48 rfl (by decide), e 7 56 rfl (by decide)]
  have hq : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 ∨ k / 8 = 4 ∨ k / 8 = 5 ∨
      k / 8 = 6 ∨ k / 8 = 7 := by omega
  rcases hq with h | h | h | h | h | h | h | h <;> simp [h]

/-- the low w bits of a number are 0 exactly if each bit below w is false -/
theorem low_bits_zero (n w : Nat) : n % 2 ^ w = 0 ↔ ∀ k, k < w → n.testBit k = false := by
  constructor
  · intro h k hk
    have := Nat.testBit_mod_two_pow n w k
    rw [h] at this
    simpa [hk] using this.symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < w
    · simp [hi, h i hi]
    · simp [hi]

/-- the two tests on one block -/
theorem passes_bits_block (w : Nat) (hw : w ≤ 64) (b : ByteArray) :
    (w == 0 || (wordAt b 0).toNat % 2 ^ w == 0) =
      (List.range w).all fun k => bitAt b k == false := by
  have key : ((wordAt b 0).toNat % 2 ^ w = 0) ↔ ∀ k, k < w → bitAt b k = false := by
    rw [low_bits_zero]
    constructor
    · intro h k hk
      rw [← wordAt_testBit _ k (by omega)]
      exact h k hk
    · intro h k hk
      rw [wordAt_testBit _ k (by omega)]
      exact h k hk
  by_cases h1 : (wordAt b 0).toNat % 2 ^ w = 0
  · have h2 := key.mp h1
    have : ((List.range w).all fun k => bitAt b k == false) = true := by
      rw [List.all_eq_true]
      intro k hk
      rw [h2 k (List.mem_range.mp hk)]
      rfl
    rw [this, h1]
    simp
  · have h0 : w ≠ 0 := fun e => h1 (by rw [e]; exact Nat.mod_one _)
    have : ((List.range w).all fun k => bitAt b k == false) = false := by
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      exact h1 (key.mpr fun k hk => by simpa using hall k (List.mem_range.mpr hk))
    rw [this]
    simp [h0, h1]

/-- For w ≤ 64, the work test in words is the work test in bits. -/
theorem passes_bits (w : Nat) (hw : w ≤ 64) (bs : Array ByteArray) :
    passesA w bs = passesBits w bs :=
  passes_bits_block w hw _

/-- at 64 bits of work the whole first word is 0 -/
theorem passes_64 (bs : Array ByteArray) :
    passesA 64 bs = (wordAt (bs.getD 0 ByteArray.empty) 0 == 0) := by
  unfold passesA
  generalize wordAt (bs.getD 0 ByteArray.empty) 0 = x
  have h1 : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt x.toNat_lt
  rw [h1]
  by_cases h : x = 0
  · subst h
    rfl
  · have h2 : x.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp e)
    have e1 : (x.toNat == 0) = false := beq_false_of_ne h2
    have e2 : (x == 0) = false := beq_false_of_ne h
    rw [e1, e2]
    rfl

end Fmt
