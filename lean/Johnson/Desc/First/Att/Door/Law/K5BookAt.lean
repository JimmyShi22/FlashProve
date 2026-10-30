-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5BookAt.lean: kind K5: **THE TWO EQUATIONS ON THE TABLE's NUMBERS (K5Book, Johnson/Desc/First/Att/K05T2.lean) WHERE THESE NUMBERS ARE READ OFF WHAT THE DESCRIPTION's SUB-PROTOCOLS TELL**
(Numbers.withTold, Johnson/Desc/First/BookNumbers.lean): a sub-protocol that tells no oracle message leaves the number of trees and the number of messages as they were.

Main names:
  k5Book_withTold: over letters: p stands at k, p' at k + 1 (by the list's own idxOf), the k-th sub-protocol tells nothing → K5Book (N.withTold ps told) p p'.
  k5_idx_full | k5_idx_full': in the full written list of places the kind's place of group g stands first at 14 (2 g + 1) + 4, the place behind it at 14 (2 g + 1) + 5: two decisions of Lean's kernel. k5_idx_bite: the negative test.
  k5Book_full: at the full written list: told[14 (2 g + 1) + 4]? = some [] → K5Book (N.withTold PFullK told) ‹the two places›.
IS IT EMPTY HERE? A rule over letters and two decisions on a written list. That the kind's sub-protocol tells nothing is a premise here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05KindR
import Johnson.Desc.First.Att.K05T2
import Johnson.Desc.First.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (K5Book)

/-- **A sub-protocol that tells nothing leaves the two numbers on the book.** -/
theorem k5Book_withTold (N : Numbers) (ps : List Place) (told : List (List Oracle)) (k : ℕ) {p p' : Place} (hp : ps.idxOf p = k)
    (hp' : ps.idxOf p' = k + 1) (ht : told[k]? = some []) : K5Book (N.withTold ps told) p p' where
  trees := by
    show treesTold told (ps.idxOf p') = treesTold told (ps.idxOf p)
    rw [hp, hp']
    unfold treesTold
    rw [List.take_add_one, ht]
    simp
  msgs := by
    show msgsTold told (ps.idxOf p') = msgsTold told (ps.idxOf p)
    rw [hp, hp']
    unfold msgsTold
    rw [List.take_add_one, ht]
    simp

set_option maxRecDepth 100000 in
theorem k5_idx_full : ∀ g, g < 12 → PFullK.idxOf ⟨1, some (2 * g + 1), 3, .K5⟩ = 14 * (2 * g + 1) + 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem k5_idx_full' : ∀ g, g < 12 → PFullK.idxOf ⟨1, some (2 * g + 1), 4, .K1⟩ = 14 * (2 * g + 1) + 4 + 1 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The negative test: the like equation at a thirteenth group is false. -/
theorem k5_idx_bite : ¬ PFullK.idxOf ⟨1, some (2 * 12 + 1), 3, .K5⟩ = 14 * (2 * 12 + 1) + 4 := by decide +kernel

/-- **At the full written list.** -/
theorem k5Book_full (N : Numbers) (told : List (List Oracle)) {g : ℕ} (hg : g < 12) (ht : told[14 * (2 * g + 1) + 4]? = some []) :
    K5Book (N.withTold PFullK told) ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩ :=
  k5Book_withTold N PFullK told _ (k5_idx_full g hg) (k5_idx_full' g hg) ht

end H2K5.Door

#print axioms H2K5.Door.k5Book_withTold
#print axioms H2K5.Door.k5_idx_full
#print axioms H2K5.Door.k5_idx_full'
#print axioms H2K5.Door.k5_idx_bite
#print axioms H2K5.Door.k5Book_full
