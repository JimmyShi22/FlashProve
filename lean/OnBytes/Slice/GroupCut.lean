-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/GroupCut.lean: every column of a written tree of the right width is cut into a group's
rows, and the length of the link's seed.

The format puts a leaf's column on the rows of a group of oracle messages (Fmt/M2Types.lean:
`groupCol`). It gives nothing if the column has not the group's width
(OnBytes/Slice/GroupColSome.lean: it gives a column if the width is right). A written oracle has
columns of one width, that of its tree. So if the tree has the group's width, every column is cut.

Main theorems.
 `colW_length`     a column of a written oracle has the width of the round's tree.
 `groupCol_col`    if the round's tree has the group's width, the column at every position of the
                   tree is cut, and the result is the value of the total function that takes a
                   default where nothing is cut.
 `seedLen_mems`    the point of the link's seed has aR + aP coordinates.
Not claimed. Nothing on what the rows hold.
-/
import OnBytes.Slice.ChainTop
import OnBytes.Slice.GroupColSome

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Run
open Fmt.M1 Fmt.M2

/-- At a position of the round's tree, the column of a written oracle has the tree's width. -/
theorem colW_length (d : PQ.RD) (o : (wRound d).Orc) (x : ℕ) (hx : x < PQ.posN d.tree) :
    (colW d o x).length = PQ.colW d.tree := by
  unfold colW
  rw [dif_pos hx, List.length_ofFn]

/-- If the round's tree has the group's width, every column of the tree is cut. -/
theorem groupCol_col (ms : List Mem) (fresh : ℕ) (d : PQ.RD) (m : (wRound d).Msg)
    (hW : PQ.colW d.tree = widthOf ms fresh) (x : ℕ) (hx : x < PQ.posN d.tree) :
    (groupCol ms fresh (colW d m.1 x)).map (·.col) =
      some ((((treeCol d m x).bind (groupCol ms fresh)).map (·.col)).getD default) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1
    (groupCol_isSome ms fresh (colW d m.1 x) ((colW_length d m.1 x hx).trans hW))
  unfold treeCol
  rw [if_pos hx, Option.bind_some, hk]
  rfl

/-- The point of the link's seed has aR + aP coordinates. -/
theorem seedLen_mems (P : Fmt.M3.Par) :
    seedLen (lg P.C.l) (lg P.Z.l) P.mems = P.aR + P.aP := by
  simp [seedLen, Fmt.M3.Par.mems, Fmt.M3.Par.mem, cubeOf, Fmt.M3.Par.aR, Fmt.M3.Par.aP, lg]

end OnBytes.Slice

#print axioms OnBytes.Slice.colW_length
#print axioms OnBytes.Slice.groupCol_col
#print axioms OnBytes.Slice.seedLen_mems
