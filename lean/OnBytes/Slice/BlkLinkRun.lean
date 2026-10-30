-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkRun.lean: the calls out of which the steps of the program's link are made, some
of them taken apart.

The steps of the link (OnBytes/Iop/Link.lean: `linkStepsVerify`) call a few blocks of
OnBytes/Iop/Foldeq.lean: a round is closed for a point, the public conditions on a table are tested,
a folded row's oracle message joins the link's group, and the columns of a stored table are read and
turned into open rows. This file says what a run of some of them, on a view, has done.

Main definitions.
 `storedList`   the listed positions of a stored table's part of a round's draws.
 `columnRows`   the rows of a table's draws, from the listed positions and the columns there.
Main theorems: `yields_samples`, `drawPoint_inv`, `foldeqRequire_inv`,
`foldeqColumnsVerify_inv`.
Not claimed. Nothing here on the call by which a folded row's oracle message joins the group.
Nothing on what a row's coefficients are. Nothing on the dry run. Nothing on soundness.
-/
import OnBytes.Iop.Link
import OnBytes.Iop.OpenLaws
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-! ## Single calls -/

/-- Reading the number of answers to a sample returns it and changes nothing. -/
theorem yields_samples (n : Nat) (c c' : Ctx) :
    Blk.samples.Yields c n c' ↔ n = c.ch.samples ∧ c' = c := by
  show (some (c.ch.samples, c) : Option (Nat × Ctx)) = some (n, c') ↔ _
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A round that was closed for a point: it was closed, and it drew the point's coordinates. -/
theorem drawPoint_inv (round : String) (count : Nat) (x : List E) (c c' : Ctx)
    (h : (drawPoint round count).Yields c x c') :
    ∃ d, (Blk.close round .elems 0).Yields c d c' ∧ x = d.elems.map E.ofTriple ∧
      x.length = count := by
  unfold drawPoint Blk.closeElems at h
  obtain ⟨x', c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨d, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 h1
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 a2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hl, e3⟩ := (Blk.yields_must _ _ _).1 h3
  obtain ⟨e4, e5⟩ := (Blk.yields_pure _ _ _ _).1 a3
  refine ⟨d, ?_, e4.trans e1, ?_⟩
  · rw [e5, e3, e2]
    exact h2
  · rw [e4]
    exact beq_iff_eq.1 hl

/-- The public conditions on a table's shape and key hold, and nothing changes. -/
theorem foldeqRequire_inv (key : TableKey) (S : FoldeqShape) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (foldeqRequire key S).Yields c () c') :
    foldeqOk c.st.codes S = true ∧ key.fits S.index = true ∧ c' = c := by
  unfold foldeqRequire at h
  obtain ⟨st, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨eS, e1⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨k2, e2⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨k3, e3⟩ := (Blk.yields_must _ _ _).1 h3
  have e3' : c3 = c := e3.trans (e2.trans e1)
  rw [e3'] at a3
  obtain ⟨_, e4⟩ := (Blk.yields_test _ _ _ hd).1 a3
  rw [eS] at k2
  exact ⟨k2, k3, e4⟩

/-- The list of a stored table's part of a round's draws: each position once, increasing, modulo the
tree's length. -/
def storedList (t : Fmt.Stored) (pos : Positions) : List Nat :=
  Fmt.listOf ((Fmt.partOf t pos.draws.toList).map (· % 2 ^ t.sh.a))

/-! ## The columns of a stored table -/

/-- The relation `Blk.SameButNotes` holds between a context and itself. -/
theorem sameButNotes_refl (c : Ctx) : Blk.SameButNotes c c := ⟨rfl, rfl, rfl, rfl⟩

/-- The relation `Blk.SameButNotes` is transitive. -/
theorem sameButNotes_trans {a b c : Ctx} (h1 : Blk.SameButNotes a b) (h2 : Blk.SameButNotes b c) :
    Blk.SameButNotes a c :=
  ⟨h2.ch.trans h1.ch, h2.st.trans h1.st, h2.book.trans h1.book, h2.failed.trans h1.failed⟩

/-- The rows of a table's draws: one for each draw, from the column that was opened at the draw's
position. list, columns: the listed positions and the columns there. -/
def columnRows (S : FoldeqShape) (eqGamma : Array E) (pos : Positions) (first : Nat)
    (u : FoldedRow) (list : Array Nat) (columns : Array (Array F)) : Option (List Row) :=
  ((pos.draws.toList.drop first).take S.columns).mapM fun x => do
    let i ← list.idxOf? x
    foldeqColumnRow S x (foldeqSymbol eqGamma (← columns[i]?)) u

/-- A run of the call that reads a table's columns and adds their rows, on a view. -/
theorem foldeqColumnsVerify_inv (key : TableKey) (S : FoldeqShape) (eqGamma : Array E)
    (pos : Positions) (first : Nat) (u : FoldedRow) (g : Nat) (c c' : Ctx)
    (hd : c.ch.dry = false)
    (h : (foldeqColumnsVerify key S eqGamma pos first u g).Yields c () c') :
    ∃ r rows c1,
      (Blk.readStored ⟨S.index.tree, S.index.saltBytes, key.item, first, S.columns⟩ pos).Yields
        c r c1 ∧
      columnRows S eqGamma pos first u r.1 r.2 = some rows ∧
      (∀ x ∈ rows, RowChecked c1.st x) ∧
      Blk.SameButNotes { c1 with st := withRows c1.st g rows } c' := by
  unfold foldeqColumnsVerify at h
  obtain ⟨_, c0, h0, a0⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, e0⟩ := (Blk.yields_must _ _ _).1 h0
  obtain ⟨r, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 a0
  rw [e0] at h1
  obtain ⟨list, columns⟩ := r
  have hd1 : c1.ch.dry = false :=
    (Blk.readStored_inv _ _ _ _ _ _ hd h1).2.2.2.1.dry.trans hd
  obtain ⟨rows, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨k2, e2⟩ := (Blk.yields_getOnView _ _ _ _ _ hd1).1 h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  rw [e2] at h3
  obtain ⟨l, k3, k4, e3⟩ := addRowsOnView_inv _ _ _ _ hd1 h3
  obtain rfl : rows = l := Option.some.inj k3
  refine ⟨(list, columns), rows, c1, h1, k2, fun x hx => (k4 x hx).2, ?_⟩
  rw [← e3]
  cases hr : rows.head? with
  | none =>
    rw [hr] at a3
    rw [((Blk.yields_pure _ _ _ _).1 a3).2]
    exact sameButNotes_refl _
  | some row =>
    rw [hr] at a3
    obtain ⟨_, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
    obtain ⟨_, c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
    refine sameButNotes_trans (Blk.yields_note _ _ _ _ h4)
      (sameButNotes_trans (Blk.yields_noteBy _ _ _ _ h5) ?_)
    split at a5
    · exact Blk.yields_noteBy _ _ _ _ a5
    · rw [((Blk.yields_pure _ _ _ _).1 a5).2]
      exact sameButNotes_refl _

end OnBytes.Slice

#print axioms OnBytes.Slice.yields_samples
#print axioms OnBytes.Slice.drawPoint_inv
#print axioms OnBytes.Slice.foldeqRequire_inv
#print axioms OnBytes.Slice.sameButNotes_refl
#print axioms OnBytes.Slice.sameButNotes_trans
#print axioms OnBytes.Slice.foldeqColumnsVerify_inv
