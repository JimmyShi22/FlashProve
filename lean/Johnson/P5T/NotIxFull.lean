-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/NotIxFull.lean: "NO NUMBER OF A SEGMENT's OWN MESSAGES IS THE INDEX MASKS' MESSAGE's",
AT THE WRITTEN VALUES, AT EACH OF THE 25 SEGMENTS AND EVERY MOMENT: BY LEAN's KERNEL. One
definition with code and six theorems. No public file is read.
  `ownFull m j`: `FillSent.ownAt` (Johnson/Desc/First/SentAtMoment.lean) at the written shape
  `shapeFull`, the written numbers `NFull`, the closed lists `At.links` and `At.ps`, AND THE
  EMPTY ARRAY in the place of the built segments.
  `ownAt_built`: **`ownAt` does not read the built segments** (rfl: they go into another field of
  the data).
  `ownAt_class`: it reads the moment j by three classes alone: j ≤ 1, j = 2, the rest.
  `notIx_full`: **by the kernel: at the moments 1, 2, 3, at all 25 segments, no own number is
  `NFull.indexNo`.**
  `notIx_counts`: what it ranges over: the index masks' number is 4; 99 own numbers at moment 3,
  from 0 to 184, none twice; SEGMENT 0's ARE 0, 1, 2, 5, 6: SO THE NUMBER 4 LIES INSIDE THAT
  SEGMENT's RUN, IN A GAP.
  `notIx_rejects`: two negative tests: with 5 (an own number of segment 0) or 184 (of segment 24)
  in the place of 4 the test holds at 24 segments alone.
  `notIx_every`: so at every moment.
Every number here was printed by the evaluator before it was typed. (One forecast of that sheet
failed: the LEAST own number was expected beside the index masks'.)
Limits. The written values alone: that they are a verifier's is another file's
(Johnson/P5T/NotIxAtMg.lean). The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.FenceFull
import Johnson.Desc.First.SentAtMoment
import Johnson.Goal.Numbers.RequestWritten
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Numbers ModelPart)
open VerifiableInference.Desc.First.FillSent (ownAt)
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- The own numbers at the written values. -/
def ownFull (m j : Nat) : Array Nat := ownAt shapeFull NFull P5J.At.links P5J.At.ps #[] m j

/-- **`ownAt` does not read the built segments.** -/
theorem ownAt_built (s : Params.ReqShape) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (b b' : Array Stages.LinkH) (m j : ℕ) : ownAt s N links ps b m j = ownAt s N links ps b' m j :=
  rfl

/-- It reads the moment by three classes. -/
theorem ownAt_class (s : Params.ReqShape) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (b : Array Stages.LinkH) (m j : ℕ) :
    ownAt s N links ps b m j = ownAt s N links ps b m 1 ∨
      ownAt s N links ps b m j = ownAt s N links ps b m 2 ∨
      ownAt s N links ps b m j = ownAt s N links ps b m 3 := by
  by_cases h1 : j ≤ 1
  · left
    unfold ownAt
    rw [if_pos h1, if_pos (Nat.le_refl 1)]
  · by_cases h2 : j = 2
    · right; left
      rw [h2]
    · right; right
      unfold ownAt
      rw [if_neg h1, if_neg h2, if_neg (by decide), if_neg (by decide)]

set_option maxRecDepth 1000000 in
/-- **By the kernel: at the three moments, at all 25 segments.** -/
theorem notIx_full :
    ((List.range 25).all fun m => [1, 2, 3].all fun j =>
      (ownFull m j).all fun o => o != NFull.indexNo) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: what it ranges over. -/
theorem notIx_counts :
    (NFull.indexNo, ((List.range 25).flatMap fun m => (ownFull m 3).toList).length,
      ((List.range 25).flatMap fun m => (ownFull m 3).toList).foldl min 1000000,
      ((List.range 25).flatMap fun m => (ownFull m 3).toList).foldl max 0,
      ((List.range 25).flatMap fun m => (ownFull m 3).toList).eraseDups.length,
      (ownFull 0 3).toList) = (4, 99, 0, 184, 99, [0, 1, 2, 5, 6]) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: with an own number in the place of the index masks' one segment fails. -/
theorem notIx_rejects :
    (((List.range 25).filter fun m => (ownFull m 3).all fun o => o != 5).length,
      ((List.range 25).filter fun m => (ownFull m 3).all fun o => o != 184).length) = (24, 24) := by
  decide +kernel

/-- **So at every moment.** -/
theorem notIx_every {m : ℕ} (hm : m < 25) (j : ℕ) :
    ((ownFull m j).all fun o => o != NFull.indexNo) = true := by
  have H := List.all_eq_true.1 notIx_full m (List.mem_range.2 hm)
  have K : ∀ i ∈ [1, 2, 3], ((ownFull m i).all fun o => o != NFull.indexNo) = true :=
    List.all_eq_true.1 H
  unfold ownFull at K ⊢
  rcases ownAt_class shapeFull NFull P5J.At.links P5J.At.ps #[] m j with e | e | e
  · rw [e]
    exact K 1 (by simp)
  · rw [e]
    exact K 2 (by simp)
  · rw [e]
    exact K 3 (by simp)

end P5T

#print axioms P5T.ownAt_built
#print axioms P5T.ownAt_class
#print axioms P5T.notIx_full
#print axioms P5T.notIx_counts
#print axioms P5T.notIx_rejects
#print axioms P5T.notIx_every
