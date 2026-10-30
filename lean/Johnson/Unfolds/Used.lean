-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Unfolds/Used.lean: the placing rule marks columns as used. Statements with their proofs;
nothing is evaluated.
  `markOf_ne` | `marks_stay` | `marks_made`: a mark is not 0; a mark stays; a segment's columns are
    marked.
  `place_used`: if one of the asks has a length above 0 and below 2 ^ (topBit + 1), then what
    `place` returns has a column p below its J at which `padding 1 p` is false.

Limits. Nothing on soundness.
-/
import Johnson.Road.FormsKeysPub

set_option autoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Road

theorem markOf_ne (g : Seg) : markOf g ≠ 0 := by
  unfold markOf
  split <;> decide

/-- A mark, once written, is never 0 again. -/
theorem marks_stay (j : Nat) : ∀ (segs : List Seg) (u : Array Nat), u.getD j 0 ≠ 0 →
    (segs.foldl markUsed u).getD j 0 ≠ 0
  | [], _, h => h
  | g :: segs, u, h => by
    rw [List.foldl_cons]
    refine marks_stay j segs _ ?_
    obtain ⟨a1, a2, a3⟩ := markUsed_get u g j
    by_cases hj : j ∈ g.pos.toList
    · by_cases hs : j < u.size
      · rw [a2 hj hs]
        exact markOf_ne g
      · exfalso
        apply h
        simp [Array.getD, hs]
    · rw [a3 hj]
      exact h

/-- A column of a segment of the list, inside the array, bears a mark. -/
theorem marks_made (j : Nat) : ∀ (segs : List Seg) (u : Array Nat), j < u.size →
    (∃ s ∈ segs, j ∈ s.pos.toList) → (segs.foldl markUsed u).getD j 0 ≠ 0
  | [], _, _, ⟨_, hs, _⟩ => absurd hs List.not_mem_nil
  | g :: segs, u, hj, ⟨s, hs, hp⟩ => by
    rw [List.foldl_cons]
    obtain ⟨a1, a2, a3⟩ := markUsed_get u g j
    rcases List.mem_cons.1 hs with e | hs'
    · subst e
      exact marks_stay j segs _ (by rw [a2 hp hj]; exact markOf_ne s)
    · exact marks_made j segs _ (by rw [a1]; exact hj) ⟨s, hs', hp⟩

/-- **The placing rule leaves a column that is no padding on an odd layer.** -/
theorem place_used (name kind : String) (asks : List SegAsk) (fl : Nat)
    (h : ∃ a ∈ asks, 0 < a.2.1 ∧ a.2.1 < 2 ^ (topBit + 1)) :
    ∃ p, p < (place name kind asks fl).J ∧ (place name kind asks fl).padding 1 p = false := by
  obtain ⟨a, ha, h0, h1⟩ := h
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem ha
  have hn : (asks.map (·.2.1)).getD i 0 = a.2.1 := by
    simp [List.getD, hi, e]
  obtain ⟨c1, c2⟩ := columnsOf_onBlocks (asks.map (·.2.1)) i 0 (topBit + 1) (by simp)
    (by rw [hn]; exact h1)
  rw [hn] at c1 c2
  have hcol := place_columns name kind asks fl i hi
  rw [hn] at hcol
  have hseg : (place name kind asks fl).segs.getD i default ∈ (place name kind asks fl).segs := by
    have hl : i < (place name kind asks fl).segs.length := by
      show i < (asks.zipIdx.map _).length
      simp [hi]
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hlt : ((place name kind asks fl).segs.getD i default).pos.getD 0 0 <
      2 ^ (place name kind asks fl).lJ := by
    rw [hcol]
    refine Nat.lt_of_lt_of_le (c2.inside 0 (by rw [c1]; exact h0)) ?_
    show _ ≤ 2 ^ max (ceilLog2 _) fl
    exact Nat.le_trans (le_two_pow_ceilLog2 _)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hsz : 0 < ((place name kind asks fl).segs.getD i default).pos.size := by
    rw [hcol, c1]
    exact h0
  have hmem : ((place name kind asks fl).segs.getD i default).pos.getD 0 0 ∈
      ((place name kind asks fl).segs.getD i default).pos.toList := by
    have e : ((place name kind asks fl).segs.getD i default).pos.getD 0 0 =
        ((place name kind asks fl).segs.getD i default).pos[0] := by
      unfold Array.getD
      rw [dif_pos hsz]
      rfl
    rw [e]
    exact Array.getElem_mem_toList hsz
  have hu : (place name kind asks fl).used.getD
      (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 ≠ 0 :=
    marks_made _ (place name kind asks fl).segs
      (Array.replicate (2 ^ (place name kind asks fl).lJ) 0)
      (by rw [Array.size_replicate]; exact hlt) ⟨_, hseg, hmem⟩
  refine ⟨((place name kind asks fl).segs.getD i default).pos.getD 0 0, hlt, ?_⟩
  show ((place name kind asks fl).used.getD
      (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 == 0 ||
    ((place name kind asks fl).used.getD
      (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 == 2 && 1 % 2 == 0)) = false
  generalize (place name kind asks fl).used.getD
    (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 = u at hu ⊢
  have e0 : (u == 0) = false := by simpa using hu
  rw [e0]
  simp

end Johnson.Unfolds

#print axioms Johnson.Unfolds.markOf_ne
#print axioms Johnson.Unfolds.marks_stay
#print axioms Johnson.Unfolds.marks_made
#print axioms Johnson.Unfolds.place_used
