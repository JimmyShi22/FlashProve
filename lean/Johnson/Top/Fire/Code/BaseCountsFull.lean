-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/BaseCountsFull.lean: AT THE FULL SIZE: «THE PINNED TREES LIE BELOW THE PIECES' BASES» AT THE SIX WRITTEN SEATS (atSix, Johnson/RunOne/KeyFillBaseAt.lean), THE WRITTEN NUMBERS OF ROUNDS (as numerals: roundsW₁ | ₂ | ₃ (KeyRoundsAtSeat.lean) are these lists) AND THE WRITTEN DATA (writtenKFull): BY BaseCounts.lean: the kernel evaluates SIX SHORT STRETCHES ALONE (the five sendings' and the ranges' test's), over the data's twin (writtenKFull_eq, Johnson/Flat/Dec/FitAtWritten.lean); of the other twenty-nine stretches nothing is claimed.
OBJECT: basesDoor atSix … writtenKFull · USER: basesAll_at_six (KeyBasesAtSix.lean) · LETTERS: none.
  low₁ | low₂ | low₃   PROVED [the kernel]: the lower bounds: chain 1: 1 · 1 · (the ranges' test) 3 · (W) 1 · chain 2: (o_u) 1 · (o_omega) 2 · chain 3: none
  bases_at_six'  PROVED
  bases_plant'   PROVED: A CONTROL ON THE SHORT LISTS: with message 0's seat moved to (100, 0) basesDoorC says no
Limits. That a record's data are the written data is said elsewhere. Public numbers alone. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.BaseCounts
import Johnson.RunOne.KeyFillBaseAt
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false

namespace LPFD
open OnBytes.Maker
open Johnson.RunOne.KeyRows23 (atSix)
open Johnson.G (writtenKFull dKeyFull writtenKFull_eq)

abbrev rsF₁ : List Nat := [2, 2, 0, 0, 9581, 0, 0, 0, 0, 0, 9220, 0, 0, 0, 0, 23, 20, 2, 1]
abbrev rsF₂ : List Nat := [0, 1, 2, 0, 1, 2, 0, 1, 1, 35, 24, 1]
abbrev rsF₃ : List Nat := [0, 0, 30, 0]
abbrev csF₁ : List Nat := [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0]
abbrev csF₂ : List Nat := [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0]
abbrev csF₃ : List Nat := [0, 0, 0, 0]

set_option maxRecDepth 1000000 in
theorem low₁ : countsLe dKeyFull.ds₁ rsF₁ csF₁ := by
  simp only [countsLe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> first | exact Nat.zero_le _ | decide +kernel

set_option maxRecDepth 1000000 in
theorem low₂ : countsLe dKeyFull.ds₂ rsF₂ csF₂ := by
  simp only [countsLe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> first | exact Nat.zero_le _ | decide +kernel

theorem low₃ : countsLe dKeyFull.ds₃ rsF₃ csF₃ := by
  simp only [countsLe]
  exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, trivial⟩

theorem six_le : 6 ≤ dKeyFull.t₁ := by
  rw [t₁_eq]
  have h : csF₁.sum = 6 := by decide
  exact h ▸ sum_le rsF₁ csF₁ dKeyFull.ds₁ low₁

theorem three_le : 3 ≤ dKeyFull.t₂ := by
  rw [t₂_eq]
  have h : csF₂.sum = 3 := by decide
  exact h ▸ sum_le rsF₂ csF₂ dKeyFull.ds₂ low₂

theorem bases_at_six' : basesDoor atSix rsF₁ rsF₂ rsF₃ writtenKFull = true := by
  rw [writtenKFull_eq]
  exact basesDoor_of_lower atSix rsF₁ rsF₂ rsF₃ csF₁ csF₂ csF₃ dKeyFull 6 9 low₁ low₂ low₃ six_le (Nat.add_le_add six_le three_le) (by decide)

theorem bases_plant' : basesDoorC (fun j => if j == 0 then (100, 0) else atSix j) rsF₁ rsF₂ rsF₃ csF₁ csF₂ csF₃ 6 9 = false := by decide

end LPFD

#print axioms LPFD.low₁
#print axioms LPFD.low₂
#print axioms LPFD.bases_at_six'
#print axioms LPFD.bases_plant'
