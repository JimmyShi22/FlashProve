-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkTies.lean: what ties the columns that a later block of the program reads to the
oracle messages that were sent.

In the joints of OnBytes/Slice/BlkJoints.lean one part is a variable: the tie. This file writes it
down, before a fold and after a fold. All that a tie says is public. It names the group's members
and where their rows begin in the group's two tables. It says that the members and the fresh mask
make up, in that order, one tree with a given number and given shapes
(OnBytes/Slice/BlkSeat.lean: `Seat`). After a fold it also says what a code switch asks of the
three folded rows (OnBytes/Slice/BlkJointCsAt.lean: `FoldedOk`) and at which point the rows were
folded.

Main definitions.
 `LayAt`       the members of a layout, none of them kept, and the first rows of their blocks.
 `GroupTie`    the tie before a fold.
 `SingleTie`   the tie after a fold.
Main theorems.
 `Seat.congr`        a seat looks at the book and at the oracle messages alone.
 `GroupTie.notes`    noting an intermediate value changes no tie before a fold.
 `SingleTie.congr`   a tie after a fold looks at the book and at the oracle messages alone.

Not claimed. That a run of the program reaches these ties.
-/
import OnBytes.Slice.BlkJointCsAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-- The members of a layout, none of them kept, and the first rows of their blocks in the
group's main table and in its mask table. -/
structure LayAt (ms : List Nat) (mainFirst maskFirst : Array (Option Nat)) (L : GroupLayout) :
    Prop where
  /-- the members -/
  members : L.members = ms.toArray
  /-- none of them is kept -/
  kept : ∀ w, w < ms.length → L.kept.getD w false = false
  /-- the first rows of their blocks in the main table -/
  mainFirst : L.mainFirst = mainFirst
  /-- the first rows of their blocks in the mask table -/
  maskFirst : L.maskFirst = maskFirst

/-- The tie before a fold at the stage s. n: the number of the tree that holds the group's
members and the fresh mask o. shapes: their shapes, the mask's last. -/
structure GroupTie (s : Sg) (n : Nat) (shapes : List OracleShape)
    (mainFirst maskFirst : Array (Option Nat)) (c : Ctx) (row : GroupRow) (L : GroupLayout)
    (o : Nat) : Prop where
  /-- the row has no form on a kept member -/
  noKept : row.kept = #[]
  /-- the members, and that they and the fresh mask are the parts of the tree -/
  seat : ∃ ms : List Nat, LayAt ms mainFirst maskFirst L ∧ Seat c (ms ++ [o]) n s.C.a shapes

/-- The tie after a fold at the stage s, before a switch to the stage s'. K: the statement's
codes. nc, nz: the numbers of the new stage's codes. pt: the point at which the rows were folded. -/
structure SingleTie (s s' : Sg) (K : Codes) (nc nz n : Nat) (shapes : List OracleShape)
    (mainFirst maskFirst : Array (Option Nat)) (pt : Fin (s.h + s.g) → GE) (c : Ctx)
    (old : SingleRows) : Prop where
  /-- what a code switch asks of the three folded rows -/
  ok : FoldedOk s s' K nc nz old
  /-- the row variables of the main table -/
  k : old.layout.k = s.h + s.g
  /-- the row variables of the mask table -/
  h : old.layout.h = s.h
  /-- the point at which the rows were folded -/
  gamma : readP (s.h + s.g) old.gamma = pt
  /-- the members, and that they and the fresh mask are the parts of the tree -/
  seat : ∃ ms : List Nat, LayAt ms mainFirst maskFirst old.layout ∧
    Seat c (ms ++ [old.fresh]) n s.C.a shapes

/-- A seat looks at the book and at the oracle messages alone. -/
theorem Seat.congr {c c' : Ctx} {ids : List Nat} {n logN : Nat} {shapes : List OracleShape}
    (h : Seat c ids n logN shapes) (hb : c'.book = c.book) (ho : c'.st.oracles = c.st.oracles) :
    Seat c' ids n logN shapes :=
  h.keeps (BookKeeps.of_eq hb) fun o x hx => ⟨x, by rw [ho]; exact hx, rfl⟩

/-- Noting an intermediate value changes no tie before a fold. -/
theorem GroupTie.notes {s : Sg} {n : Nat} {shapes : List OracleShape}
    {mainFirst maskFirst : Array (Option Nat)} {c c' : Ctx} {row : GroupRow} {L : GroupLayout}
    {o : Nat} (h : GroupTie s n shapes mainFirst maskFirst c row L o)
    (hn : Blk.SameButNotes c c') : GroupTie s n shapes mainFirst maskFirst c' row L o := by
  obtain ⟨ms, h1, h2⟩ := h.seat
  exact ⟨h.noKept, ms, h1, h2.congr hn.book (by rw [hn.st])⟩

/-- A tie after a fold looks at the book and at the oracle messages alone. -/
theorem SingleTie.congr {s s' : Sg} {K : Codes} {nc nz n : Nat} {shapes : List OracleShape}
    {mainFirst maskFirst : Array (Option Nat)} {pt : Fin (s.h + s.g) → GE} {c c' : Ctx}
    {old : SingleRows} (h : SingleTie s s' K nc nz n shapes mainFirst maskFirst pt c old)
    (hb : c'.book = c.book) (ho : c'.st.oracles = c.st.oracles) :
    SingleTie s s' K nc nz n shapes mainFirst maskFirst pt c' old := by
  obtain ⟨ms, h1, h2⟩ := h.seat
  exact ⟨h.ok, h.k, h.h, h.gamma, ms, h1, h2.congr hb ho⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.Seat.congr
#print axioms OnBytes.Slice.GroupTie.notes
#print axioms OnBytes.Slice.SingleTie.congr
