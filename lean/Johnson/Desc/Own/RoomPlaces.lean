-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/RoomPlaces.lean: what "n ≤ roomOf" (Johnson/Desc/Own/Room.lean) gives for the
places of the table at which a vector's first n entries lie. Theorems. No block imports this file.

RoomMeans.lean's le_roomOf speaks of numbers of entries (entryAt of a place of the pad). Here the
same is said of the table's places, through the layout's own function index (entry j lies at the
table's index "index j"; in an index the row's number is the low part, index % 2 ^ rowBits, and the
place in the row the high part, index / 2 ^ rowBits).
  entryAt_index   entryAt is the inverse of index on the table: for j below
                  2 ^ rowBits * 2 ^ placeBits.
  room_in_table   1 ≤ n ≤ roomOf: every j < n is below 2 ^ rowBits * 2 ^ placeBits.
  room_rows       1 ≤ n ≤ roomOf: every entry j < n LIES IN A REAL ROW: its row's number is below
                  the shape's number of main rows.
  room_places     the same, GIVEN that 2 ^ placeBits is the code's message length ell (ell is a
                  power of two): every entry j < n lies at a real place of its row: the place's
                  number is below ell.
  room_off_pad    1 ≤ n ≤ roomOf: NO ENTRY j < n LIES AT A PLACE OF THE SAMPLE's PAD in the main
                  table.
What is not claimed. THAT THE ENTRY LIES AT A REAL PLACE OF ITS ROW WHATEVER ell IS: a row of the
table has 2 ^ placeBits places, placeBits being the least a with ell ≤ 2 ^ a; where ell is no power
of two, the places from ell on are no entries of the message, and roomOf counts them. Whoever calls
roomOf asks by a clause of its own what it needs of ell. Nothing on soundness.

-/
import Johnson.Desc.Own.RoomMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem le_pow_ceil (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  by_cases h : n ≤ 1
  · simp only [h, if_true, Nat.pow_zero]
  · simp only [h, if_false]
    have := @Nat.lt_log2_self (n - 1)
    omega

/-- entryAt is the inverse of index on the table. -/
theorem entryAt_index (l : VectorLay) (j : Nat) (h : j < 2 ^ l.rowBits * 2 ^ l.placeBits) :
    l.entryAt (l.index j) = j := by
  unfold VectorLay.entryAt VectorLay.index
  cases l.rowsHigh with
  | false => rfl
  | true =>
    have hR : 0 < 2 ^ l.rowBits := Nat.two_pow_pos _
    have ha : j / 2 ^ l.placeBits < 2 ^ l.rowBits :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    simp only [if_true]
    rw [Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt ha, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt ha, Nat.zero_add, Nat.mul_comm]
    exact Nat.mod_add_div j (2 ^ l.placeBits)

theorem room_in_table (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (n : Nat) (h1 : 1 ≤ n)
    (h : n ≤ roomOf codes s rowsHigh) (j : Nat) (hj : j < n) :
    j < 2 ^ (vectorLay codes s rowsHigh).rowBits * 2 ^ (vectorLay codes s rowsHigh).placeBits := by
  have h2 := ((le_roomOf codes s rowsHigh n h1).1 h).2.1
  have h3 : s.mainRows ≤ 2 ^ (vectorLay codes s rowsHigh).rowBits := le_pow_ceil s.mainRows
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hj h2) (Nat.mul_le_mul_right _ h3)

/-- **The first n entries lie in real rows.** -/
theorem room_rows (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (n : Nat) (h1 : 1 ≤ n)
    (h : n ≤ roomOf codes s rowsHigh) (j : Nat) (hj : j < n) :
    (vectorLay codes s rowsHigh).index j % 2 ^ (vectorLay codes s rowsHigh).rowBits <
      s.mainRows := by
  obtain ⟨hc, h2, -⟩ := (le_roomOf codes s rowsHigh n h1).1 h
  have hc := ((roomCan_iff codes s rowsHigh).1 hc).1
  have hR : 0 < 2 ^ (vectorLay codes s rowsHigh).rowBits := Nat.two_pow_pos _
  cases rowsHigh with
  | false =>
    have e : s.mainRows = 2 ^ (vectorLay codes s false).rowBits := by
      cases hc with
      | inl x => cases x
      | inr x => exact x
    have : (vectorLay codes s false).index j = j := rfl
    rw [this]
    exact Nat.lt_of_lt_of_eq (Nat.mod_lt _ hR) e.symm
  | true =>
    have ha : j / 2 ^ (vectorLay codes s true).placeBits < s.mainRows :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact Nat.lt_of_lt_of_le hj h2)
    have hi : (vectorLay codes s true).index j =
        j / 2 ^ (vectorLay codes s true).placeBits +
          (j % 2 ^ (vectorLay codes s true).placeBits) * 2 ^ (vectorLay codes s true).rowBits := rfl
    rw [hi, Nat.add_mul_mod_self_right]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha

/-- **Where the code's message length is a power of two** (2 ^ placeBits is that length), the first
n entries lie at real places of their rows: the place's number is below the message length. -/
theorem room_places (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (n : Nat) (h1 : 1 ≤ n)
    (h : n ≤ roomOf codes s rowsHigh) (j : Nat) (hj : j < n)
    (hE : 2 ^ (vectorLay codes s rowsHigh).placeBits = (codes.base.getD s.code default).ell) :
    (vectorLay codes s rowsHigh).index j / 2 ^ (vectorLay codes s rowsHigh).rowBits <
      (codes.base.getD s.code default).ell := by
  have ht := room_in_table codes s rowsHigh n h1 h j hj
  have hR : 0 < 2 ^ (vectorLay codes s rowsHigh).rowBits := Nat.two_pow_pos _
  have hP : 0 < 2 ^ (vectorLay codes s rowsHigh).placeBits := Nat.two_pow_pos _
  rw [← hE]
  cases rowsHigh with
  | false =>
    have : (vectorLay codes s false).index j = j := rfl
    rw [this]
    exact Nat.div_lt_of_lt_mul ht
  | true =>
    have ha : j / 2 ^ (vectorLay codes s true).placeBits < 2 ^ (vectorLay codes s true).rowBits :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ht)
    have hi : (vectorLay codes s true).index j =
        j / 2 ^ (vectorLay codes s true).placeBits +
          (j % 2 ^ (vectorLay codes s true).placeBits) * 2 ^ (vectorLay codes s true).rowBits := rfl
    rw [hi, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt ha, Nat.zero_add]
    exact Nat.mod_lt _ hP

/-- **None of the first n entries lies at a place of the pad.** -/
theorem room_off_pad (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (n : Nat) (h1 : 1 ≤ n)
    (h : n ≤ roomOf codes s rowsHigh) (j : Nat) (hj : j < n) (p : PadPlace)
    (hp : p ∈ (if s.answers == 0 then [] else (padMade codes s).getD [])) (hm : p.part = .main) :
    (vectorLay codes s rowsHigh).index j ≠ p.index := by
  intro e
  have h3 := ((le_roomOf codes s rowsHigh n h1).1 h).2.2 p hp hm
  rw [← e, entryAt_index _ j (room_in_table codes s rowsHigh n h1 h j hj)] at h3
  omega

end VerifiableInference.Desc.Own
