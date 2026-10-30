-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPiecesF.lean: the virtual rows of the pieces of the smallness test's
two lookup calls, from the success of the routine that makes them.

HTailF2.piecesF lays one piece for each block of ZZ's rows and each of the two calls: the low call's
piece of block i reads through virtual row i of ZZ, the high call's through row n + i, where n is
the number of blocks. placeZ then gives each piece its range of keys; it turns neither a piece's
array nor its virtual row, nor the order of the list.

 - placeZ_keys: the pieces of placeZ's call have the arrays and virtual rows of the pieces given.
 - piecesF_keys: if piecesF, run on tl, returns tl', then tl' has tl's numbers of arrays (ix),
   matrices' arrays (gtTree) and number of matrices (NM), and the (array, virtual row) of the pieces
   of tl', the low call's first, are (ZZ, 0), .., (ZZ, 2 n - 1), with n = tl'.zzBlocks and ZZ =
   tl'.ix.ZZ.
 - pieces_apart: so they differ from each other; pieces_low: each is a row of ZZ below zzRowReads;
   pieces_not_powers: so it is neither of ZZ's two rows under powers.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that the state has these rows. Nor is anything claimed on BZ's number or on the
matrices' arrays (HTailF2.shapeF lays them).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

private theorem ok_bind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ok_jp {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- A piece's array and virtual row. -/
def keyOfPiece (p : Piece) : Nat × Nat := (p.tree, p.row)

theorem list_modify_key (f : Piece → Piece) (hf : ∀ p, keyOfPiece (f p) = keyOfPiece p) :
    ∀ (l : List Piece) (i : Nat), (l.modify i f).map keyOfPiece = l.map keyOfPiece
  | [], _ => by simp
  | p :: l, 0 => by simp [hf]
  | p :: l, i + 1 => by simp [list_modify_key f hf l i]

theorem map_modify_key (a : Array Piece) (i : Nat) (f : Piece → Piece)
    (hf : ∀ p, keyOfPiece (f p) = keyOfPiece p) :
    (a.modify i f).toList.map keyOfPiece = a.toList.map keyOfPiece := by
  rw [Array.toList_modify]
  exact list_modify_key f hf _ _

/-- placeZ turns no piece's array or virtual row, nor the order of the list. -/
theorem placeZ_keys (pieces : Array Piece) (name : String) (k lid : Nat) :
    (placeZ pieces name k lid).pieces.toList.map keyOfPiece = pieces.toList.map keyOfPiece := by
  have hs : (pieces.map fun p =>
      { p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp }).toList.map
        keyOfPiece = pieces.toList.map keyOfPiece := by
    rw [Array.toList_map, List.map_map]
    rfl
  have hf : ∀ (g : Nat → Nat) (l : List Nat) (s : Array Piece × Nat),
      (l.foldl (fun (s : Array Piece × Nat) i =>
        (s.1.modify i (fun p => { p with off := s.2 }), s.2 + 2 ^ g i)) s).1.toList.map keyOfPiece =
        s.1.toList.map keyOfPiece := by
    intro g l
    induction l with
    | nil => intro s; rfl
    | cons i l ih =>
      intro s
      rw [List.foldl_cons, ih]
      exact map_modify_key _ _ _ fun _ => rfl
  rw [← hs]
  exact hf _ _ _

theorem allPieces_keys (tl : HTailF2) :
    (allPieces tl).map (fun a => (a.2.tree, a.2.row)) =
      tl.z1.pieces.toList.map keyOfPiece ++ tl.z2.pieces.toList.map keyOfPiece := by
  unfold allPieces
  rw [List.map_append, List.map_map, List.map_map]
  rfl

/-- The pieces' arrays and virtual rows, from the maker's success. -/
theorem piecesF_keys {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    tl'.ix = tl.ix ∧ tl'.gtTree = tl.gtTree ∧ tl'.NM = tl.NM ∧
      (allPieces tl').map (fun a => (a.2.tree, a.2.row)) =
        (List.range (2 * tl'.zzBlocks)).map fun i => (tl'.ix.ZZ, i) := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := ok_bind h
  obtain ⟨_, h⟩ := ok_jp h
  obtain ⟨_, h⟩ := ok_jp h
  obtain ⟨f9, _, h⟩ := ok_bind h
  obtain ⟨pub, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  have e := (Except.ok.inj h).symm
  subst e
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [allPieces_keys]
  show (placeZ _ _ _ _).pieces.toList.map keyOfPiece ++
    (placeZ _ _ _ _).pieces.toList.map keyOfPiece = (List.range (2 * bz.size)).map _
  rw [placeZ_keys, placeZ_keys, Array.toList_map, Array.toList_map, Array.toList_range,
    List.map_map, List.map_map, Nat.two_mul, List.range_add, List.map_append, List.map_map]
  rfl

theorem pieces_apart {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    ((allPieces tl').map fun a => (a.2.tree, a.2.row)).Nodup := by
  rw [(piecesF_keys h).2.2.2]
  exact List.Nodup.map (fun _ _ e => (Prod.mk.inj e).2) List.nodup_range

theorem pieces_low {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') (a : Nat × Piece)
    (ha : a ∈ allPieces tl') : a.2.tree = tl'.ix.ZZ ∧ a.2.row < tl'.zzRowReads := by
  have hm : (a.2.tree, a.2.row) ∈ (allPieces tl').map fun a => (a.2.tree, a.2.row) :=
    List.mem_map.2 ⟨a, ha, rfl⟩
  rw [(piecesF_keys h).2.2.2] at hm
  obtain ⟨i, hi, e⟩ := List.mem_map.1 hm
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  exact ⟨e1.symm, by rw [← e2]; exact List.mem_range.1 hi⟩

/-- No piece's row is one of ZZ's two rows under powers. -/
theorem pieces_not_powers {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') (a : Nat × Piece)
    (ha : a ∈ allPieces tl') :
    ¬ (tl'.ix.ZZ = a.2.tree ∧ tl'.zzRowReads = a.2.row) ∧
      ¬ (tl'.ix.ZZ = a.2.tree ∧ tl'.zzRowTies = a.2.row) := by
  have h1 := (pieces_low h a ha).2
  have h2 : tl'.zzRowTies = tl'.zzRowReads + 1 := rfl
  exact ⟨fun e => by omega, fun e => by omega⟩

end Fo
