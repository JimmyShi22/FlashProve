-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/EqHands.lean: THE RECORD's HALF OF THE TABLE's PROMISE BEHIND A YES OF
THE ONE EQUATION's BLOCK: the four Bools that read the record and the plan's numbers alone (where
the chain stands; the open rows' lists; the groups' members; where the book stands), each behind the
block from itself in front. Theorems: EqLays.lean (what the yes does to the record) laid on
RowsPush.lean (what the table's tests say of such a push) and ShapeRides.lean's `shape_step`.

What is said.
  `rows_size`: where the test on the rows holds and a class of segment m is open, m's group's list
    has as many rows as the open classes count. `eq_rows`, `eq_members`, `eq_book`, `eq_shape`:
    **the four Bools behind the block**, at the table's own step of the open set; `eq_mark`: a mark
    stays, and none is laid. The row of the table is a letter r with r.ins = [the total of m],
    r.outs = [the class «equation» of m].

Limits. PREMISES ON PUBLIC DATA, shown here of no numbers: the class is not open in front, another
class of m is; the plan lays the class at the end of what is open, one row; no other open segment
has m's group; the plan counts as many trees and messages at the two places; the two places are
neighbours of one link with one stand. ONE PREMISE ON THE RECORD THAT NONE OF THE FOUR BOOLS GIVES:
THE GROUP THAT THE LINK's RECORD NAMES IS THE PLAN's GROUP OF m (hg). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.EqLays
import Johnson.Desc.First.Link.Law.RowsPush
import Johnson.Desc.First.Link.Law.ShapeRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Item RowClass BlockRow Numbers stepOpen rowSegs rowsDue
  rowsHeld membersHeld bookAt shapeAt)

variable (N : Numbers)

/-- Where the test on the rows holds, an open segment's group's list has as many rows as the open
classes count. -/
theorem rows_size (O : List Item) (s : S) (m : ℕ) (G : Group) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) (h : rowsHeld N O s = true) :
    G.rows.size = rowsDue N O m := by
  rw [rowsHeld_eq, List.all_eq_true] at h
  have h0 := h m hm
  unfold segOk at h0
  rw [hG] at h0
  simp only [] at h0
  have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h0).1).2
  simpa using h2

/-- **The open rows' lists, behind the one equation.** -/
theorem eq_rows (O : List Item) (r : BlockRow) (m : ℕ) (hins : r.ins = [.total m])
    (houts : r.outs = [.row m .equation]) (fresh : Item.row m .equation ∉ O)
    (seg : m ∈ rowSegs O) (hat : N.rowsAt m .equation = (rowsDue N O m, 1))
    (inj : ∀ m' ∈ rowSegs O, m' ≠ m → N.groupAt m' ≠ N.groupAt m) (s s' : S) (g : ℕ)
    (row : OnBytes.Row) (G : Group) (E : EqLays s s' g row) (hG : s.st.groups[g]? = some G)
    (hg : N.groupAt m = g) (h : rowsHeld N O s = true) : rowsHeld N (stepOpen O r) s' = true := by
  rw [First.rowsHeld_of_filter N (O ++ [.row m .equation]) (stepOpen O r)
    (stepOpen_row O r _ (by rw [hins]; simp [Item.isRow]) houts fresh)]
  refine rowsHeld_push N O m g G row s s' hg hG E.groups (fun m' h1 h2 => hg ▸ inj m' h1 h2) seg ?_
    E.kind h
  rw [hat, rows_size N O s m G seg (by rw [hg]; exact hG) h]

/-- **The groups' members, behind the one equation.** -/
theorem eq_members (O : List Item) (r : BlockRow) (m : ℕ) (hins : r.ins = [.total m])
    (houts : r.outs = [.row m .equation]) (fresh : Item.row m .equation ∉ O)
    (seg : m ∈ rowSegs O) (s s' : S) (g : ℕ) (row : OnBytes.Row) (E : EqLays s s' g row)
    (h : membersHeld N O s = true) : membersHeld N (stepOpen O r) s' = true := by
  rw [First.membersHeld_of_filter N (O ++ [.row m .equation]) (stepOpen O r)
    (stepOpen_row O r _ (by rw [hins]; simp [Item.isRow]) houts fresh)
    (stepOpen_pins O r _ (by rw [hins]; simp [Item.isPin]) houts rfl)]
  exact membersHeld_push N O m g row s s' E.groups (by rw [E.book]) seg h

/-- **Where the book stands, behind the one equation.** -/
theorem eq_book (p p' : Option Place) (ht : N.treesAt p' = N.treesAt p)
    (hm : N.msgsAt p' = N.msgsAt p) (s s' : S) (g : ℕ) (row : OnBytes.Row)
    (E : EqLays s s' g row) (h : bookAt N p s = true) : bookAt N p' s' = true := by
  unfold bookAt at h ⊢
  rw [E.book, E.oracles, ht, hm]
  exact h

/-- **Where the chain stands, behind the one equation: no count of rows waits.** -/
theorem eq_shape (links : List ModelPart) (p p' : Place) (hn : NextIn links p p') (s s' : S) (g : ℕ)
    (row : OnBytes.Row) (E : EqLays s s' g row) (h : shapeAt links (some p) s = true) :
    shapeAt links (some p') s' = true :=
  shape_step links p p' s s' h E.stand hn.stand hn.link
    (Or.inl (by unfold S.noneWaits; rw [E.owed])) E.num

/-- A mark stays, and none is laid. -/
theorem eq_mark (s s' : S) (g : ℕ) (row : OnBytes.Row) (E : EqLays s s' g row) :
    s'.failed = s.failed := E.failed

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.eq_rows
#print axioms VerifiableInference.Desc.LinkJoin.eq_members
#print axioms VerifiableInference.Desc.LinkJoin.eq_book
#print axioms VerifiableInference.Desc.LinkJoin.eq_shape
