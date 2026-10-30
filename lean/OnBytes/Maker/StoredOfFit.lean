-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/StoredOfFit.lean: the test `storedFit` on the plain data of a file
(OnBytes/Maker/WholeOf.lean) gives `StoredSecond` (OnBytes/Maker/StoredRoot.lean): the first and the
third chain open no stored table.

A statement and its proof. `storedOwed_of_read` (OnBytes/Maker/OwesOfRead.lean) and the laws above
it ask `StoredSecond`. It is the first half of the test by its body. `storedAt_of_fit`
(OnBytes/Maker/TypeFileOfRead.lean) gives `StoredAt` from the same test.

Main name: `storedSecond_of_fit`.
Limits: that the test says yes is a premise. Nothing on soundness.


-/
import OnBytes.Maker.WholeOf
import OnBytes.Maker.StoredRoot

set_option autoImplicit false

namespace OnBytes.Maker

/-- **The test on the stored tables: the second chain alone opens one.** -/
theorem storedSecond_of_fit {a : ℕ} {W : Three.Whole} (h : storedFit a W = true) :
    StoredSecond W := by
  unfold storedFit at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact ⟨fun d hd => List.isEmpty_iff.1 (h.1 d (List.mem_append_left _ hd)),
    fun d hd => List.isEmpty_iff.1 (h.1 d (List.mem_append_right _ hd))⟩

end OnBytes.Maker
