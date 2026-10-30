-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/RoomMeans.lean: what roomCan and roomOf (Johnson/Desc/Own/Room.lean) say, as
statements in Prop, and that roomOf is the hand-written program's vectorRoom. Theorems. No block
imports this file.

  roomCan_iff     roomCan = true ↔ its three clauses as statements; the third by what padMade's
                  returning means in numbers (padMade_isSome_iff is not imported here: the
                  clause stays "padMade returns").
  le_belowPad     n ≤ belowPad lay places m ↔ n ≤ m, and n ≤ the entry's number at every place of
                  the pad that lies in the main table.
  le_roomOf       **WHAT "n ≤ roomOf" MEANS**, for 1 ≤ n: the message can hold a vector in this
                  layout (roomCan); n is at most the number of places of the real rows; and every
                  place of the sample's pad in the main table holds an entry whose number is at
                  least n. Both directions. (Under roomCan padMade returns wherever there is a
                  sample: the "getD []" in the statement is never at nothing.) THAT THE ENTRIES
                  0, …, n - 1 THEN LIE IN REAL ROWS AND NONE OF THEM AT A PLACE OF THE PAD is drawn
                  beside, in Johnson/Desc/Own/RoomPlaces.lean (room_rows · room_off_pad).
  room_needs      1 ≤ n ≤ roomOf gives roomCan: the three hidden tests are asked by every such
                  clause.
  roomOf_eq       roomOf = vectorRoom, at all arguments.
What is not claimed. THAT THE ENTRIES LIE AT REAL PLACES OF THEIR ROWS: that wants the code's
message length to be a power of two (lengthsFit of the same codes; RoomPlaces.lean: room_places).
That a caller asks the right n. Nothing on soundness.

-/
import Johnson.Desc.Own.Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem roomCan_iff (codes : Codes) (s : OracleShape) (rowsHigh : Bool) :
    roomCan codes s rowsHigh = true ↔
      (rowsHigh = true ∨ s.mainRows = 2 ^ (vectorLay codes s rowsHigh).rowBits) ∧
      (vectorLay codes s rowsHigh).bits ≤ 60 ∧
      (s.answers = 0 ∨ (padMade codes s).isSome = true) := by
  unfold roomCan
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

theorem le_belowPad (lay : VectorLay) (n : Nat) : ∀ (places : List PadPlace) (m : Nat),
    n ≤ belowPad lay places m ↔
      n ≤ m ∧ ∀ p ∈ places, p.part = .main → n ≤ lay.entryAt p.index
  | [], m => by simp [belowPad]
  | p :: l, m => by
    have ih := le_belowPad lay n l
    unfold belowPad at ih ⊢
    rw [List.foldl_cons, ih]
    by_cases hp : p.part = .main
    · simp only [hp, beq_self_eq_true, if_true, Nat.le_min, List.mem_cons, forall_eq_or_imp,
        true_implies, and_assoc]
    · have hb : (p.part == Part.main) = false := by simpa using hp
      simp only [hb, Bool.false_eq_true, if_false, List.mem_cons, forall_eq_or_imp, hp,
        false_implies, true_and]

/-- 1 ≤ n ≤ roomOf: the three hidden tests have said yes. -/
theorem room_needs (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (n : Nat) (h1 : 1 ≤ n)
    (h : n ≤ roomOf codes s rowsHigh) : roomCan codes s rowsHigh = true := by
  unfold roomOf at h
  by_cases hc : roomCan codes s rowsHigh = true
  · exact hc
  · simp only [hc, Bool.false_eq_true, if_false] at h
    omega

/-- **What "n ≤ roomOf" means.** -/
theorem le_roomOf (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (n : Nat) (h1 : 1 ≤ n) :
    n ≤ roomOf codes s rowsHigh ↔
      roomCan codes s rowsHigh = true ∧
      n ≤ s.mainRows * 2 ^ (vectorLay codes s rowsHigh).placeBits ∧
      ∀ p ∈ (if s.answers == 0 then [] else (padMade codes s).getD []), p.part = .main →
        n ≤ (vectorLay codes s rowsHigh).entryAt p.index := by
  constructor
  · intro h
    have hc := room_needs codes s rowsHigh n h1 h
    unfold roomOf at h
    simp only [hc, if_true] at h
    exact ⟨hc, (le_belowPad _ n _ _).1 h⟩
  · rintro ⟨hc, h⟩
    unfold roomOf
    simp only [hc, if_true]
    exact (le_belowPad _ n _ _).2 h

/-- roomOf is the program's vectorRoom. -/
theorem roomOf_eq (codes : Codes) (s : OracleShape) (rowsHigh : Bool) :
    roomOf codes s rowsHigh = vectorRoom codes s rowsHigh := by
  have hpad : padMade codes s = Send.pad codes s := rfl
  unfold roomOf roomCan vectorRoom belowPad
  simp only [hpad]
  cases rowsHigh <;> by_cases h1 : s.mainRows = 2 ^ (vectorLay codes s false).rowBits <;>
    by_cases h2 : (vectorLay codes s false).bits ≤ 60 <;>
    by_cases h2' : (vectorLay codes s true).bits ≤ 60 <;>
    by_cases h3 : s.answers = 0 <;>
    cases h4 : Send.pad codes s <;>
    first
      | (simp_all [Nat.not_le]; done)
      | (simp_all [Nat.not_le]; intro h; omega)

end VerifiableInference.Desc.Own
