-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsKeeps.lean: what a run of the program's code switch keeps.

A run of the program's proximity test is taken apart block by block. What one block has recorded of
trees and oracle messages must hold when a later block reads them. This file shows that a run of the
code switch (OnBytes/Slice/BlkCsRun.lean: `CsRan`) keeps what is public of the book of trees (which
oracle messages share a tree, and where) and of the statement (OnBytes/Slice/BlkSeat.lean:
`BookKeeps`, `ShapesKeep`), the codes, and that it stays a run on the same view (`OnView`; a view,
`Fmt.View`, holds a proof's rounds and opened columns).

Main theorems: `CsRan.bookKeeps`, `CsRan.shapesKeep`, `CsRan.codes`, `CsRan.onView`,
`CsRan.roots_eq`.
Not claimed. Where the new oracle messages are in the book. Nothing on soundness.
-/
import OnBytes.Slice.BlkCsLay
import OnBytes.Slice.BlkSentSeat

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## What a run of the code switch keeps -/

section
variable {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- Reading the old rows, on a view, keeps what `ReadKeeps` lists: what is public of the book, the
number of roots received, the number of answers to a sample. -/
theorem singleRowsRead_keeps (s : SingleRows) (pos : Positions) (y : Array E) (a a' : Ctx)
    (hd : a.ch.dry = false) (h : (singleRowsRead s pos).Yields a y a') : ReadKeeps a a' := by
  obtain ⟨opened, h1, _⟩ := singleRowsRead_inv s pos y a a' h
  exact readOpened_keeps _ _ _ _ _ hd h1

/-- A run of the switch keeps what is public of the book. -/
theorem CsRan.bookKeeps (h : CsRan old T gp others c c' out row lay theta D) :
    BookKeeps c.book c'.book := by
  have h1 : BookKeeps c.book D.cB.book := by
    rw [h.bookB]
    exact bookSent_keeps c _ D.lay
  have h2 := (singleRowsRead_keeps old _ D.y D.cB D.cC h.dryB h.read).book
  rw [h.book]
  exact h1.trans h2

/-- A run of the switch has received one root for each new tree. -/
theorem CsRan.roots_eq (h : CsRan old T gp others c c' out row lay theta D) :
    c'.ch.roots = c.ch.roots + D.lay.shapes.size := by
  exact h.roots

/-- After a run of the switch each oracle message has the shape that it had after the sending. -/
theorem CsRan.shape_at (h : CsRan old T gp others c c' out row lay theta D) (i : Nat) :
    (c'.st.oracles[i]?).map (·.shape)
      = ((stSent c.st (sentOf T others)).oracles[i]?).map (·.shape) := by
  rw [h.st]
  show ((closeLedgers (D.stR T gp others c) _).oracles[i]?).map (·.shape) = _
  rw [closeLedgers_shape]
  unfold CsTaken.stR CsTaken.stJ CsTaken.stA
  rw [(withRows_oracles gp D.rows _).1, joined_shape, (ledgerShut_shape _ T _ i).2, admitted_shape]

/-- A run of the switch keeps each older oracle message, with its shape. -/
theorem CsRan.shapesKeep (h : CsRan old T gp others c c' out row lay theta D) :
    ShapesKeep c.st c'.st := by
  intro o x hx
  have ho : o < c.st.oracles.size := by
    rcases Nat.lt_or_ge o c.st.oracles.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hx
      cases hx
  have h1 := h.shape_at o
  rw [stSent_old c.st _ o ho, hx] at h1
  cases hx' : c'.st.oracles[o]? with
  | none => rw [hx'] at h1; cases h1
  | some x' => rw [hx'] at h1; exact ⟨x', rfl, Option.some.inj h1⟩

/-- A run of the switch changes no code. -/
theorem CsRan.codes (h : CsRan old T gp others c c' out row lay theta D) :
    c'.st.codes = c.st.codes := by
  rw [h.st]
  show (closeLedgers (D.stR T gp others c) _).codes = _
  rw [closeLedgers_codes]
  exact (D.stR_shape T gp others c).1

/-- A run of the switch on a view stays a run on that view. -/
theorem CsRan.onView (h : CsRan old T gp others c c' out row lay theta D) (V : Fmt.View)
    (hv : OnView V c) : OnView V c' := by
  have hB : OnView V D.cB :=
    ⟨h.dryB, h.firstB.trans hv.first, fun o ho => hv.opened o (h.openedB ▸ ho)⟩
  have hC : OnView V D.cC := by
    obtain ⟨opened, h1, _⟩ := singleRowsRead_inv old _ D.y D.cB D.cC h.read
    exact (readOpened_shows V _ _ _ _ _ hB h1).1
  exact ⟨h.dry, h.firstTree.trans hv.first, fun o ho => hC.opened o (h.opened ▸ ho)⟩

end

end OnBytes.Slice

#print axioms OnBytes.Slice.CsRan.bookKeeps
#print axioms OnBytes.Slice.CsRan.roots_eq
#print axioms OnBytes.Slice.CsRan.shapesKeep
#print axioms OnBytes.Slice.CsRan.codes
#print axioms OnBytes.Slice.CsRan.onView
#print axioms OnBytes.Slice.singleRowsRead_keeps
#print axioms OnBytes.Slice.CsRan.shape_at
