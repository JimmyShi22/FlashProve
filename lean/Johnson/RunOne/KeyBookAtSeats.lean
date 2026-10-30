-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyBookAtSeats.lean: THE KEY FILE's SHARED CHAIN: THE TABLES' PROMISE HANDS THE PROXIMITY TESTS' LAWS THEIR GUARD BEHIND THE DOOR. A K12 law's WHOLE promise at a seat is, at the record t behind the door in: FIRST ARM (seat_of_book, K12/Coin/FirstBook.lean:135): t.mask.isSome = true ∧ BookOrd π.nums.firstTree t.book · THE OWN MASK's ARM (seat_of_bookOwn, FirstBookOwn.lean:159): t.mask = none ∧ BookStep π.nums.firstTree t.book t.roots. Seat.enter (K12/Seat.lean:44) copies the chain's record's book and roots and reads the mask off its small record. shape₂'s LAST clause is bookStepB 0 d.book d.roots; its eighth: behind o_u's sending: l.firstMask == some 1.
OBJECT: the guards of the laws at rows 2.9 | 2.10 · USER: whoever calls seat_of_book | seat_of_bookOwn at the key file's shared chain · LETTERS: S a d.
  bookStep_of_shape₂   PROVED: at every border k
  guard_29             PROVED: at border 9, at Seat.onGu's door
  guard_210            PROVED: at border 10, at Seat.onGomega's door
THE LAWS SPEAK AT π.nums.firstTree; THESE AT 0: that the two places' firstTree is 0 is a public fact on the plan, NOT SAID HERE (an evaluation on the honest walk, told in a text of ours, not in this repository, saw «first = 0»).
THE TABLES NAME NO K12 LAW: which form a payer calls is its own choice. Nothing on soundness.
-/
import Johnson.RunOne.BorderShapes.LKFU.Shape23
import Johnson.Desc.Sound.BookInOrder
import Johnson.Desc.K12.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Sound (BookOrd BookStep bookStepB bookStep_iff)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enter)

theorem bookStep_of_shape₂ (S : LinShape) (a k : Nat) (d : _root_.Desc.K14.St) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k d) = true) :
    BookStep 0 d.book d.roots := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb⟩ := h
  exact (bookStep_iff 0 d.book d.roots).1 hb

theorem guard_29 (S : LinShape) (a : Nat) (d : _root_.Desc.K14.St) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 9 d) = true) (t : T12)
    (ht : enter (·.gU) (·.firstMask) d = .ok t) : t.mask.isSome = true ∧ BookOrd 0 t.book := by
  have hB := bookStep_of_shape₂ S a 9 d h
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := h
  have hm : d.loc.firstMask = some 1 := by
    rw [if_neg (by decide)] at h8
    simpa using (Bool.and_eq_true_iff.1 h8).2
  cases ht
  exact ⟨by show d.loc.firstMask.isSome = true; rw [hm]; rfl, hB.2⟩

theorem guard_210 (S : LinShape) (a : Nat) (d : _root_.Desc.K14.St) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 10 d) = true) (t : T12)
    (ht : enter (·.gOmega) (fun _ => none) d = .ok t) : t.mask = none ∧ BookStep 0 t.book t.roots := by
  have hB := bookStep_of_shape₂ S a 10 d h
  cases ht
  exact ⟨rfl, hB⟩

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.bookStep_of_shape₂
#print axioms Johnson.RunOne.KeyRows23.guard_29
#print axioms Johnson.RunOne.KeyRows23.guard_210
