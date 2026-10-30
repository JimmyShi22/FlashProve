-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCuts.lean: the format can cut the columns of the written trees.

The standard readings of a transcript (OnBytes/Slice/SemLib.lean) take the column of a written tree
at a position and put it on rows as the format does: `col1` on the rows of the first group, `colSt`
on the rows of a later stage. Both are total: they take a default where the format cannot cut the
column. This file shows that the format can cut every column of a tree that has the right width, so
that the default is never taken. The form is the one that the files on the program
(OnBytes/Slice/Blk*.lean) use: for a column that the round's tree shows at a position.

Main theorems.
 `takeE_some`, `cutCol_some`, `stageCol_some`: a list of words of the right length is cut.
 `colSt_cut`: a column of a later stage's tree is cut, and the result is `colSt`.
 `col1_cut`: a column of the first tree is cut, and the result's rows are `col1`.
 `foldWords_std`: the three folded words of the words that are read off columns are `wordMid`.

Not claimed. That a tree has the width that is asked. Nothing on what is in the rows.
-/
import OnBytes.Slice.SemLib
import OnBytes.Slice.FoldPeel

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Run

/-! ## A list of words of the right length is cut -/

/-- n symbols can be taken off a list of 3 n + r words, and a list of r words is left. -/
theorem takeE_some : ∀ (n : ℕ) (w : List UInt64) (r : ℕ), w.length = 3 * n + r →
    ∃ l w', Fmt.M1.takeE n w = some (l, w') ∧ w'.length = r
  | 0, w, r, h => ⟨[], w, rfl, by omega⟩
  | n + 1, a :: b :: c :: w, r, h => by
    have hw : w.length = 3 * n + r := by
      simp only [List.length_cons] at h
      omega
    obtain ⟨l, w', e, hl⟩ := takeE_some n w r hw
    refine ⟨(a, b, c) :: l, w', ?_, hl⟩
    show (Fmt.M1.takeE n w).map _ = _
    rw [e]
    rfl
  | n + 1, [], r, h => by
    simp only [List.length_nil] at h
    omega
  | n + 1, [_], r, h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | n + 1, [_, _], r, h => by
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- A column without main symbols over the base field, of the right length, is cut. -/
theorem cutCol_some (mE nz : ℕ) (w : List UInt64) (h : w.length = 3 * mE + 3 * nz) :
    ∃ x, Fmt.M1.cutCol 0 mE nz w = some x := by
  obtain ⟨me, w', e1, hl⟩ := takeE_some mE w (3 * nz) h
  obtain ⟨zs, w'', e2, _⟩ := takeE_some nz w' 0 (by omega)
  refine ⟨((w.take 0).map Fmt.Fld.ofF ++ me, zs), ?_⟩
  unfold Fmt.M1.cutCol
  rw [if_pos (by rw [h, Nat.zero_add]; exact beq_self_eq_true _), List.drop_zero, e1]
  show (Fmt.M1.takeE nz w').map _ = _
  rw [e2]
  rfl

/-- A column of a later stage's tree, of the right length, is put on rows. -/
theorem stageCol_some (st : Fmt.M1.Stage) (mE : ℕ) (w : List UInt64)
    (h : w.length = 3 * mE + 3 * (2 * 2 ^ st.h)) : ∃ col, Fmt.M1.stageCol st 0 mE w = some col := by
  obtain ⟨x, e⟩ := cutCol_some mE (2 * 2 ^ st.h) w h
  unfold Fmt.M1.stageCol
  rw [e]
  exact ⟨_, rfl⟩

/-! ## The columns of the written trees -/

/-- A position at which a round's tree shows a column is a position of the tree. -/
theorem treeCol_lt (d : PQ.RD) (m : (wRound d).Msg) (x : ℕ) (w : List UInt64)
    (h : treeCol d m x = some w) : x < PQ.posN d.tree := by
  unfold treeCol at h
  split at h
  · assumption
  · cases h

/-- A column of a later stage's tree is cut, and the result is the standard reading's, if a column
has three words for each of the stage's 2^(h + g) main rows and 2 * 2^h mask rows (`hW`). -/
theorem colSt_cut (s : Sg) (d : PQ.RD) (m : (wRound d).Msg)
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h)) (x : ℕ) (w : List UInt64)
    (h : treeCol d m x = some w) :
    Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g)) w = some (colSt s d m.1 x) := by
  have hx := treeCol_lt d m x w h
  obtain rfl := treeCol_some d m x w h
  obtain ⟨col, e⟩ := stageCol_some s.st (2 ^ (s.h + s.g)) (colW d m.1 x)
    ((colW_length d m.1 x hx).trans hW)
  have hc : colSt s d m.1 x = col := by
    show (Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g)) (colW d m.1 x)).getD default = col
    rw [e]
    rfl
  rw [hc, e]

/-- A column of the first tree is cut, and the result's rows are the standard reading's, if a column
has the width of the group's members and one fresh mask row (`hW`). -/
theorem col1_cut (S : Sz) (d : PQ.RD) (m : (wRound d).Msg)
    (hW : PQ.colW d.tree = Fmt.M2.widthOf S.P.mems 1) (x : ℕ) (w : List UInt64)
    (h : treeCol d m x = some w) :
    ∃ kc, Fmt.M2.groupCol S.P.mems 1 w = some kc ∧ col1 S d m.1 x = kc.col := by
  have hx := treeCol_lt d m x w h
  obtain rfl := treeCol_some d m x w h
  obtain ⟨kc, e⟩ := Option.isSome_iff_exists.1
    (groupCol_isSome S.P.mems 1 (colW d m.1 x) ((colW_length d m.1 x hx).trans hW))
  refine ⟨kc, e, ?_⟩
  unfold col1
  rw [e]
  rfl

/-! ## The folded words -/

/-- The three folded words (`foldWords`) of the words that are read off columns are `wordMid`. -/
theorem foldWords_std (s : Sg) (col : ℕ → Fmt.M1.Col) (γ : Fin (s.h + s.g) → GE) :
    foldWords s (wordIn s col) (wordFr s col) γ = wordMid s col γ :=
  rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.takeE_some
#print axioms OnBytes.Slice.cutCol_some
#print axioms OnBytes.Slice.stageCol_some
#print axioms OnBytes.Slice.treeCol_lt
#print axioms OnBytes.Slice.colSt_cut
#print axioms OnBytes.Slice.col1_cut
#print axioms OnBytes.Slice.foldWords_std
