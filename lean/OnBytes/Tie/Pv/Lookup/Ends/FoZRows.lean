-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoZRows.lean.
The tests on public numbers of the lookup on the digits: each piece's rows lie inside its array.

The pieces of the two calls are blocks of rows of the array ZZ. HTailF2.piecesF takes the blocks
from t2BL at the record's tau, and each lies within the rows 0 to tau - 1; placeZ turns no piece's
first row or number of rows. HTailF2.addTreesF lays ZZ with tau rows
(OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean). So the last clause of Fo.ZTests follows from the success
of these two routines. That the blocks tile these rows is not shown here: it is a clause of
tailTest, which stays a premise.

Main names:
  `t2BL_le`: t2BL R = .ok o gives x.1 + x.2 ≤ R for every block x of o.
  `placeZ_rows`: placeZ turns no piece's first row or number of rows, nor the order of the list.
  `piecesF_rows`: tl.piecesF = .ok tl' gives a.2.r0 + a.2.Rp ≤ tl'.tau for every piece a of tl'.
The walk of placeZ follows OnBytes/Tie/Pv/Lookup/Forest/FoPiecesF.lean's.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZRec
import OnBytes.Tie.Pv.Lookup.Ends.FoAddTrees

set_option autoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

/-! ### the blocks -/

theorem t2BLLoop_le (R : ℕ) : ∀ (fuel r0 : ℕ), ∀ x ∈ t2BLLoop R fuel r0, x.1 + x.2 ≤ R
  | 0, _, x, hx => by
    rw [t2BLLoop] at hx
    cases hx
  | fuel + 1, r0, x, hx => by
    rw [t2BLLoop] at hx
    split at hx
    · rename_i hlt
      rcases List.mem_cons.1 hx with rfl | hx
      · show r0 + 2 ^ Nat.log2 (R - r0) ≤ R
        have := Nat.log2_self_le (n := R - r0) (by omega)
        omega
      · exact t2BLLoop_le R fuel _ x hx
    · cases hx

theorem t2BL_le {R : ℕ} {o : Array (ℕ × ℕ)} (h : t2BL R = .ok o) :
    ∀ x ∈ o.toList, x.1 + x.2 ≤ R := by
  unfold t2BL at h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    intro x hx
    exact t2BLLoop_le R _ _ x (by simpa using hx)

/-! ### placeZ -/

/-- A piece's first row and number of rows. -/
def rowsOf (p : Piece) : ℕ × ℕ := (p.r0, p.Rp)

theorem list_modify_rows (f : Piece → Piece) (hf : ∀ p, rowsOf (f p) = rowsOf p) :
    ∀ (l : List Piece) (i : ℕ), (l.modify i f).map rowsOf = l.map rowsOf
  | [], _ => by simp
  | p :: l, 0 => by simp [hf]
  | p :: l, i + 1 => by simp [list_modify_rows f hf l i]

theorem map_modify_rows (a : Array Piece) (i : ℕ) (f : Piece → Piece)
    (hf : ∀ p, rowsOf (f p) = rowsOf p) :
    (a.modify i f).toList.map rowsOf = a.toList.map rowsOf := by
  rw [Array.toList_modify]
  exact list_modify_rows f hf _ _

theorem placeZ_rows (pieces : Array Piece) (name : String) (k lid : ℕ) :
    (placeZ pieces name k lid).pieces.toList.map rowsOf = pieces.toList.map rowsOf := by
  have hs : (pieces.map fun p =>
      { p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp }).toList.map
        rowsOf = pieces.toList.map rowsOf := by
    rw [Array.toList_map, List.map_map]
    rfl
  have hf : ∀ (g : ℕ → ℕ) (l : List ℕ) (s : Array Piece × ℕ),
      (l.foldl (fun (s : Array Piece × ℕ) i =>
        (s.1.modify i (fun p => { p with off := s.2 }), s.2 + 2 ^ g i)) s).1.toList.map rowsOf =
        s.1.toList.map rowsOf := by
    intro g l
    induction l with
    | nil => intro s; rfl
    | cons i l ih =>
      intro s
      rw [List.foldl_cons, ih]
      exact map_modify_rows _ _ _ fun _ => rfl
  rw [← hs]
  exact hf _ _ _

/-! ### the pieces -/

theorem piecesF_rows {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    ∀ a ∈ allPieces tl', a.2.r0 + a.2.Rp ≤ tl'.tau := by
  unfold piecesF at h
  obtain ⟨bz, hb, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨f9, _, h⟩ := bindX h
  obtain ⟨pub, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  have e := (Except.ok.inj h).symm
  subst e
  have key : ∀ (row : ℕ → ℕ) (c0 : ℕ) (name : String) (k : ℕ),
      ∀ p ∈ (placeZ ((Array.range bz.size).map fun i =>
        ({ tree := tl.ix.ZZ, row := row i, r0 := (bz.getD i (0, 0)).1,
           Rp := (bz.getD i (0, 0)).2, c0 := c0, Cp := tl.mz } : Piece)) name k
          tl.lidb).pieces.toList, p.r0 + p.Rp ≤ tl.tau := by
    intro row c0 name k p hp
    have hm : rowsOf p ∈ (placeZ _ name k tl.lidb).pieces.toList.map rowsOf :=
      List.mem_map_of_mem hp
    rw [placeZ_rows, Array.toList_map, Array.toList_range, List.map_map] at hm
    obtain ⟨i, hi, e⟩ := List.mem_map.1 hm
    have hi' : i < bz.size := List.mem_range.1 hi
    have hx : bz.getD i (0, 0) ∈ bz.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
      exact Array.getElem_mem_toList hi'
    have := t2BL_le hb _ hx
    have e1 : (bz.getD i (0, 0)).1 = p.r0 := congrArg Prod.fst e
    have e2 : (bz.getD i (0, 0)).2 = p.Rp := congrArg Prod.snd e
    omega
  intro a ha
  unfold allPieces at ha
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact key (fun i => i) 0 _ _ p hp
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact key (fun i => bz.size + i) tl.mz _ _ p hp

end Fo.ZPlan
