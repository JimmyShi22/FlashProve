-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/BasePinsTie.lean: THE WRITTEN LISTS OF PINS (BasePins.lean) ARE OUR TABLES' OWN, and a yes of the test at them gives the four facts on bases that the key file's frame asks.
Main names. `pins₁_tie` | `pins₂_tie` | `pins₃_tie`: at every border up to the lists' ends (and two beyond): `pinned (open_j n)` is the written list [the kernel] · `pins₁_no`: a test that such a comparison can fail · `basesAll_of_door`: at a description whose three flat lists are no longer than the written lists: a yes of `basesDoor` at the blocks' numbers of declared rounds gives `basesAll` (BasesOk.lean): from which `four_of_all` gives hb₁ · hb₂₀ · hb₂₁₁ · hb₃₁.
OBJECT: the tables' lists of open pins · USER: KeyBasesAtSix.lean · LETTERS: at_ · F · D.
Limits. Nothing is evaluated at a description here. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.BasesOk
import Johnson.Top.Fire.Code.BasePins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows1 (open₁)
open Johnson.RunOne.KeyRows23 (open₂ open₃)

theorem pins₁_tie : ∀ n, n < 22 → pinned (open₁ 2 n) = pinW pinsW₁ n := by decide +kernel
theorem pins₂_tie : ∀ n, n < 15 → pinned (open₂ n) = pinW pinsW₂ n := by decide +kernel
theorem pins₃_tie : ∀ n, n < 7 → pinned (open₃ n) = pinW pinsW₃ n := by decide +kernel

/-- A test that such a comparison can fail. -/
theorem pins₁_no : ¬ pinned (open₁ 2 16) = [0, 1] := by decide +kernel

/-- **A yes at the written lists gives the test at the tables' own.** -/
theorem basesAll_of_door {XI : Type} (at_ : Where) (F : FileDescription XI) (D : WholeD)
    (h₁ : F.first.blocksInOrder.length ≤ 22) (h₂ : F.shared.blocksInOrder.length ≤ 15) (h₃ : F.second.blocksInOrder.length ≤ 7)
    (h : basesDoor at_ (F.first.blocksInOrder.map (·.rounds.length)) (F.shared.blocksInOrder.map (·.rounds.length)) (F.second.blocksInOrder.map (·.rounds.length)) D = true) :
    basesAll at_ F D = true := by
  rw [basesAll_eq]
  unfold basesDoor at h
  simp only [basesAllN, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.length_map] at h ⊢
  refine ⟨⟨fun n hn j hj => h.1.1 n hn j ?_, fun n hn j hj => h.1.2 n hn j ?_⟩, fun n hn j hj => h.2 n hn j ?_⟩
  · rw [← pins₁_tie n (Nat.lt_of_lt_of_le hn h₁)]; exact hj
  · rw [← pins₂_tie n (Nat.lt_of_lt_of_le hn h₂)]; exact hj
  · rw [← pins₃_tie n (Nat.lt_of_lt_of_le hn h₃)]; exact hj

end LPFD

#print axioms LPFD.pins₁_tie
#print axioms LPFD.pins₂_tie
#print axioms LPFD.pins₃_tie
#print axioms LPFD.pins₁_no
#print axioms LPFD.basesAll_of_door
