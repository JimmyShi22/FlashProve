-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LaidOffPad.lean: a cheap test, by blocks, that no element of a laid array
sits at a place of a message's pad; and the theorem that ties the test to the plain test padB,
element by element. Definitions with code and theorems. No Mathlib.

Why. "No place that a reader's seats name for a borrowed matrix is a pad's place of either copy" is
asked at every row of symbols and every column: some 10 ^ 8 elements at the full size. An array is
laid in a few blocks (Johnson/Desc/LaidAt.lean), each a whole rectangle of its message's table; the
pad of a message's main table is the last one or three places of its last main row
(Johnson/Desc/SeatAt.lean: padB). So it is enough to hold each block's last row and last place
against the pad.

What is said.
  lastRowOf b, lastPlaceOf b   the last row and the last place of the block's rectangle.
  laidIn_le      an element that the block holds lies at a row and a place no later than these.
  blockMiss cs s b   the block ends above the last main row of a message of the shape s, or ends in
                 front of the pad's places.
  missB cs s a   THE TEST: the shape has a mask row (then its pad lies in the mask table, and padB
                 says no at every main place), or every block of the array a misses.
  **padB_off**   missB cs s a = true and laidAt a i c = some (r, p) give
                 padB cs s false r p = false.

What it does not give. One way alone: a no of the test shows nothing. Which array, which shape and
which copies are to be asked is the caller's. Nothing on the mask table. Nothing on soundness.

-/
import Johnson.Desc.LaidAt
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (LaidBlock ReqArray)
open VerifiableInference.Desc (laidIn laidAt padB)

/-- The last row of the block's rectangle in its message's table. -/
def lastRowOf (b : LaidBlock) : Nat :=
  b.firstRow + (2 ^ b.bitsC * 2 ^ b.bitsI - 1) / 2 ^ b.placeBits

/-- The last place of the block's rectangle. -/
def lastPlaceOf (b : LaidBlock) : Nat := b.firstPlace + (2 ^ b.placeBits - 1)

/-- Two digits make a number below the product of their bounds. -/
theorem two_digits {a b A B : Nat} (ha : a < A) (hb : b < B) : a * B + b ≤ A * B - 1 := by
  have h1 : (a + 1) * B ≤ A * B := Nat.mul_le_mul_right B ha
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- **An element that the block holds lies no later than the block's last row and last place.** -/
theorem laidIn_le {b : LaidBlock} {i c r p : Nat} (h : laidIn b i c = some (r, p)) :
    r ≤ lastRowOf b ∧ p ≤ lastPlaceOf b := by
  unfold laidIn at h
  split at h
  · rename_i hin
    obtain ⟨h1, h2, h3, h4⟩ := hin
    have hi : i - b.firstI < 2 ^ b.bitsI := by omega
    have hc : c - b.firstC < 2 ^ b.bitsC := by omega
    have hx : (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
        else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)) ≤ 2 ^ b.bitsC * 2 ^ b.bitsI - 1 := by
      split
      · exact two_digits hc hi
      · rw [Nat.mul_comm (2 ^ b.bitsC)]
        exact two_digits hi hc
    have e := Option.some.inj h
    have e1 : b.firstRow + (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
        else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)) / 2 ^ b.placeBits = r :=
      congrArg Prod.fst e
    have e2 : b.firstPlace + (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
        else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)) % 2 ^ b.placeBits = p :=
      congrArg Prod.snd e
    have hp : 0 < 2 ^ b.placeBits := Nat.pos_of_ne_zero (by simp)
    refine ⟨?_, ?_⟩
    · rw [← e1]
      exact Nat.add_le_add_left (Nat.div_le_div_right hx) _
    · rw [← e2]
      have := Nat.mod_lt (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
        else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)) hp
      unfold lastPlaceOf
      omega
  · cases h

/-- The block ends above the last main row, or in front of the pad's places. -/
def blockMiss (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (b : LaidBlock) : Bool :=
  decide (lastRowOf b + 1 < s.mainRows) ||
    decide (lastPlaceOf b + (if s.mainDeg = 3 then 1 else 3) < (cs.base.getD s.code default).ell)

/-- **THE TEST.** -/
def missB (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (a : ReqArray) : Bool :=
  s.maskRows != 0 || a.blocks.all (blockMiss cs s)

/-- **Under the test no element of the array sits at a place of the main table's pad.** -/
theorem padB_off {cs : OnBytes.Codes} {s : OnBytes.OracleShape} {a : ReqArray}
    (hm : missB cs s a = true) {i c r p : Nat} (h : laidAt a i c = some (r, p)) :
    padB cs s false r p = false := by
  unfold padB
  rw [if_neg (by decide)]
  unfold missB at hm
  rcases Eq.mp (Bool.or_eq_true _ _) hm with h0 | h0
  · have : (s.maskRows == 0) = false := by
      cases e : (s.maskRows == 0)
      · rfl
      · rw [bne, e] at h0
        cases h0
    rw [this]
    rfl
  · unfold laidAt at h
    obtain ⟨b, hb, hl⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨hr, hp⟩ := laidIn_le hl
    have hbm := List.all_eq_true.1 h0 b hb
    unfold blockMiss at hbm
    rcases Eq.mp (Bool.or_eq_true _ _) hbm with k | k
    · have k' := of_decide_eq_true k
      have : (r + 1 == s.mainRows) = false := by
        apply beq_false_of_ne
        omega
      rw [this, Bool.and_false, Bool.false_and]
    · have k' := of_decide_eq_true k
      have : decide ((cs.base.getD s.code default).ell ≤ p + if s.mainDeg = 3 then 1 else 3) =
          false := by
        apply decide_eq_false
        omega
      rw [this, Bool.and_false]

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.laidIn_le
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padB_off
