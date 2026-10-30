-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/EarlyArrays.lean: one tie for the smallness test: the arrays whose cells the typed
block's letters count as committed before the matrix is drawn (`early`,
OnBytes/Tie/Pv/Tail/LettersAt.lean) are, as a list, the symbol arrays of all matrices and what
stands in the first four places of the record's list of vectors.

Why. The letters cut the committed entries by the Boolean `early tl`. A law on the order of sending
walks a list of arrays. That the list has just the arrays of the early cells is what lets the one be
spent for the other.

Main names:
  `early_iff_arrays`: `early tl (.cell t r c) = true` if and only if t is in
    `tl.gtTree.toList ++ (List.range 4).filterMap fun n => tl.ix.U.getD n none`.
  `early_mask`: an entry of the mask row is never early.

Limits. A fact on two texts over one record: nothing on when an array is sent, on which message it
lies in, or on which record a run has in front of the draw. Row and column are not read. The
direction from left to right stands also in Johnson/Desc/First/TailClaims/LayAtTest.lean
(`early_arraysOf`), whose steps this proof follows.
For proofs only; no module that runs imports this file.

-/
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.Ok
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Road.Rows

/-- **The arrays of the early cells, as a list.** -/
theorem early_iff_arrays (tl : HTailF2) (t r c : ℕ) :
    early tl (.cell t r c) = true ↔
      t ∈ tl.gtTree.toList ++ (List.range 4).filterMap fun n => tl.ix.U.getD n none := by
  unfold early
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_append]
  refine or_congr Iff.rfl ⟨fun h => List.mem_filterMap.2 ?_, fun h => ?_⟩
  · obtain ⟨i, hi, e⟩ := List.mem_take_iff_getElem.1 h
    refine ⟨i, List.mem_range.2 (by omega), ?_⟩
    have hlt : i < tl.ix.U.size := by
      have := hi
      simp only [Array.length_toList] at this
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    simpa using e
  · obtain ⟨n, hn, e⟩ := List.mem_filterMap.1 h
    have hn4 : n < 4 := List.mem_range.1 hn
    have hlt : n < tl.ix.U.size := by
      by_contra hc
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at e
      simp at e
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt] at e
    refine List.mem_take_iff_getElem.2 ⟨n, ?_, ?_⟩
    · simp only [Array.length_toList]
      omega
    · simpa using e

/-- An entry of the mask row is never early. -/
theorem early_mask (tl : HTailF2) (slot : ℕ) : early tl (.mask slot) = false := rfl

end Johnson.Desc.Ok

#print axioms Johnson.Desc.Ok.early_iff_arrays
#print axioms Johnson.Desc.Ok.early_mask
