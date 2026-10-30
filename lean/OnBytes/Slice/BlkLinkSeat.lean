-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkSeat.lean: where the link's oracle messages sit in the book of trees.

A later block of the program reads opened columns of the tree that holds the link's oracle messages.
What it needs to know of that tree is public and is gathered in one record
(OnBytes/Slice/BlkSeat.lean: `Seat`): the tree's number and size, the words of each part in a
column, and the place and shape of each oracle message. This file shows that the record holds after
a run of the link's steps and of the batching, if the link's message is put in one tree, by the
general law on a newly sent tree (OnBytes/Slice/BlkSentSeat.lean: `seat_of_sent`).

Main definition: `maskShape`, the shape of the fresh mask of the test's first fold.
Main theorems: `linkSt_oracle2`, `linkSt_shape`, `begun_shape`, `LinkRan.bat_seat`.
Not claimed. That the link's message is put in one tree is a hypothesis here.
-/
import OnBytes.Slice.BlkLinkHead
import OnBytes.Slice.BlkSentSeat

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-- The shape of the fresh mask of the test's first fold. -/
abbrev maskShape (S : LinkShape) : OracleShape := (foldMaskNotice (linkFoldShape S)).shape

/-- The fresh mask's oracle message after the link's steps, if masks are sent ahead. -/
theorem linkSt_oracle2 (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
    (rows0 rows1 : List Row) (rE : Row) (hm : S.masksAhead = true) :
    (linkSt S T places s0 s1 rows0 rows1 rE).oracles[T.oracles.size + 2]? =
      some { shape := maskShape S } := by
  have q2 : (stSent (withGroup T S.code S.maskCode)
      (linkMessage S 1)).oracles[T.oracles.size + 2]? = some { shape := maskShape S } :=
    (linkSent_oracles S (withGroup T S.code S.maskCode)).2.2 hm
  have h0 : T.oracles.size ≠ T.oracles.size + 2 := by omega
  have h1 : T.oracles.size + 1 ≠ T.oracles.size + 2 := by omega
  unfold linkSt
  rw [(withRow_oracles _ _ _).1, (withRows_oracles _ _ _).1, (withRows_oracles _ _ _).1,
    joined_other _ _ _ _ _ _ h1, joined_other _ _ _ _ _ _ h0, admitted_other _ _ _ _ _ _ h1,
    admitted_other _ _ _ _ _ _ h0, q2]

/-- The statement after the link's steps has the shapes of the statement after the receiving. -/
theorem linkSt_shape (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
    (rows0 rows1 : List Row) (rE : Row) (i : Nat) :
    ((linkSt S T places s0 s1 rows0 rows1 rE).oracles[i]?).map (·.shape) =
      ((stSent T (linkMessage S 1)).oracles[i]?).map (·.shape) := by
  unfold linkSt
  rw [(withRow_oracles _ _ _).1, (withRows_oracles _ _ _).1, (withRows_oracles _ _ _).1,
    joined_shape, joined_shape, admitted_shape, admitted_shape]
  rfl

/-- The beginning of a test changes no shape. -/
theorem begun_shape (S : Statement) (g : Nat) (G : Group) (i : Nat) :
    ((begun S g G).oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape) :=
  closeLedgers_shape _ _ _

section
variable {S : LinkShape} {first further : TableKey} {c c1 c2 : Ctx} {x : LinkRun} {D : LinkData}
  (hR : LinkRan S first further c c1 x D)
  {G : Group} {L : GroupLayout} {θ : E} {row : GroupRow} (hB : BatRan x.group c1 c2 G L θ row)

include hR hB

/-- Where the link's oracle messages sit, after the batching: they are the parts of one tree, if
the link's message is put in one tree sh. cf: a context that differs from the one after the
batching in kept values alone. -/
theorem LinkRan.bat_seat (sh : TreeShape) (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (linkMessage S 1).size → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols =
      (((linkMessage S 1).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols =
      (((linkMessage S 1).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray)
    (cf : Ctx) (hn : Blk.SameButNotes c2 cf) :
    Seat cf ((List.range (linkMessage S 1).size).map (· + c.st.oracles.size))
      (c.ch.firstTree + c.ch.roots) sh.logN ((linkMessage S 1).toList.map (·.shape)) := by
  refine seat_of_sent c cf (linkMessage S 1) D.lay sh hR.placed ?_ (fun i => ?_) h1 ht hmain hmask
  · rw [hn.book]
    exact (hR.bat_keeps hB).2.1
  · rw [hn.st, hB.st, begun_shape, hR.st, linkSt_shape]

end

end OnBytes.Slice

#print axioms OnBytes.Slice.linkSt_oracle2
#print axioms OnBytes.Slice.linkSt_shape
#print axioms OnBytes.Slice.begun_shape
#print axioms OnBytes.Slice.LinkRan.bat_seat
