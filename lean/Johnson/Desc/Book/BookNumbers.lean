-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/BookNumbers.lean: ON A CHAIN THAT RECEIVES ALL ITS TREES, A TREE's NUMBER IN THE
BOOK IS ITS PLACE IN THE ORDER OF SENDING. An invariant of the plain ground's record
(Johnson/Desc/First/Base/DescState.lean: DState), over Johnson/Desc/Book/BookFitsGround.lean.
Definitions, statements and proofs.
  recvP_roots     the receiving: as many roots more as the layout has trees.
  adoptP_roots, and thirteen "..._roots" : no other routine of the ground turns the number of roots
                  received.
  Numbered ft d   as many roots are received as the book has trees; and the tree at place j has the
                  number ft + j and the source "own root number j". ft: the number of the chain's
                  first tree.
  numbered_start  it holds of a record with no tree and no root.
  recvP_numbered  THE RECEIVING AT THE SAME ft KEEPS IT.
  numbered_same   a routine that leaves book and roots as they are keeps it: so the thirteen do.
  adopt_breaks    THE ADOPTING DOES NOT KEEP IT: it lays a tree and receives no root.
What is not said. THAT EVERY RECEIVING OF A CHAIN IS HANDED THE SAME ft: recvP takes it at every
call: the caller's. That a chain writes its book by the plain ground alone: it does not (see
BookFitsGround.lean's head): the walk is not read here. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Book.BookFitsGround
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground

variable {L : Type}

/-! ## The number of roots received -/

/-- The receiving: as many roots more as the layout has trees. -/
theorem recvP_roots (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) :
    ∃ lay, layTrees d.st.codes sent = some lay ∧ d'.roots = d.roots + lay.shapes.size := by
  unfold recvP at h
  rw [Own.treesMade_eq] at h
  split at h
  · cases hl : layTrees d.st.codes sent with
    | none => simp [hl] at h
    | some lay =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨lay, rfl, rfl⟩
  · cases h

/-- The adopting receives no root. -/
theorem adoptP_roots (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) : d'.roots = d.roots := by
  unfold adoptP at h
  rw [Own.treesMade_eq] at h
  split at h
  · cases hl : layTrees d.st.codes sent with
    | none => simp [hl] at h
    | some lay =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  · cases h


theorem newGroupP_roots (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : d'.roots = d.roots := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · cases h

theorem admitP_roots (d d' : DState L) (o : Nat) (rows : Array Row)
    (h : admitP d o rows = some d') : d'.roots = d.roots := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    rfl
  · cases h

theorem joinP_roots (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : d'.roots = d.roots := by
  unfold joinP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      subst h
      rfl
  · cases h

theorem addRowP_roots (d d' : DState L) (g : Nat) (row : Row)
    (h : addRowP d g row = some d') : d'.roots = d.roots := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

theorem addRowsFrom_roots (g : Nat) (rows : List Row) : ∀ (d d' : DState L),
    addRowsFrom g rows d = some d' → d'.roots = d.roots := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    rfl
  | cons row l ih =>
    intro d d' h
    simp only [addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact (ih e d' h).trans (addRowP_roots d e g row h1)

theorem addRowsP_roots (d d' : DState L) (g : Nat) (rows : List Row)
    (h : addRowsP d g rows = some d') : d'.roots = d.roots := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_roots g rows d d' h
  · cases h

theorem takeMaskP_roots (d d' : DState L) (o n : Nat)
    (h : takeMaskP d o = some (n, d')) : d'.roots = d.roots := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  · cases h

theorem takeMasksInto_roots (o : Nat) (count : Nat) : ∀ (d d' : DState L) (acc : Array Nat)
    (r : List Nat), takeMasksInto o count d acc = some (r, d') → d'.roots = d.roots := by
  induction count with
  | zero =>
    intro d d' acc r h
    simp only [takeMasksInto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | succ n ih =>
    intro d d' acc r h
    simp only [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e h1
      exact (ih e d' _ r h).trans (takeMaskP_roots d e o i h1)

theorem takeMasksP_roots (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : d'.roots = d.roots :=
  takeMasksInto_roots o count d d' #[] r h

theorem closeLedgerP_roots (d d' : DState L) (o : Nat)
    (h : closeLedgerP d o = some d') : d'.roots = d.roots := by
  unfold closeLedgerP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

theorem spendAsMaskP_roots (d d' : DState L) (o : Nat)
    (h : spendAsMaskP d o = some d') : d'.roots = d.roots := by
  unfold spendAsMaskP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

theorem beginRunP_roots (d d' : DState L) (g : Nat) (r : RunInput)
    (h : beginRunP d g = some (r, d')) : d'.roots = d.roots := by
  unfold beginRunP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  · cases h

theorem elsewhereP_roots (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : d'.roots = d.roots := by
  unfold elsewhereP at h
  split at h
  · cases hy : other.oracles[theirs]? with
    | none => simp [hy] at h
    | some y =>
      simp only [hy, Option.map_some, Option.some.injEq] at h
      subst h
      rfl
  · cases h


/-! ## A tree's number is its place -/

/-- **As many roots as trees; the tree at place j has the number ft + j and its own root j.** -/
def Numbered (ft : Nat) (d : DState L) : Prop :=
  d.roots = d.book.trees.size ∧
    ∀ (j : Nat) (t : Tree), d.book.trees[j]? = some t → t.number = ft + j ∧ t.src = .own j

theorem numbered_start (ft : Nat) (d : DState L) (h0 : d.roots = 0) (hB : d.book.trees = #[]) :
    Numbered ft d := by
  refine ⟨by rw [h0, hB]; rfl, fun j t h => ?_⟩
  rw [hB] at h
  exact absurd (Array.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_zero _)

/-- **THE RECEIVING AT THE SAME ft KEEPS IT.** -/
theorem recvP_numbered (ft : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP ft d sent = some (ids, d')) (hN : Numbered ft d) : Numbered ft d' := by
  obtain ⟨_, lay, hl, S⟩ := recvP_seat ft d d' sent ids h
  obtain ⟨lay', hl', hr⟩ := recvP_roots ft d d' sent ids h
  obtain rfl : lay = lay' := Option.some.inj (hl.symm.trans hl')
  obtain ⟨n1, n2⟩ := hN
  refine ⟨by rw [hr, S.size, n1], fun j t ht => ?_⟩
  by_cases lt : j < d.book.trees.size
  · rw [S.trees j lt] at ht
    exact n2 j t ht
  · have lt' := (Array.getElem?_eq_some_iff.1 ht).1
    rw [S.size] at lt'
    obtain ⟨τ, rfl⟩ : ∃ τ, j = d.book.trees.size + τ := ⟨j - d.book.trees.size, by omega⟩
    obtain ⟨t', a, _, e2, e3, _, _⟩ := S.made τ (by omega)
    obtain rfl : t = t' := Option.some.inj (ht.symm.trans a)
    rw [n1] at e2 e3
    exact ⟨e2, e3⟩

/-- A routine that leaves book and roots as they are keeps it. -/
theorem numbered_same (ft : Nat) (d d' : DState L) (hb : d'.book = d.book)
    (hr : d'.roots = d.roots) (hN : Numbered ft d) : Numbered ft d' := by
  unfold Numbered
  rw [hb, hr]
  exact hN

/-- **The adopting does not keep it** where it lays a tree: a tree more, and no root more. -/
theorem adopt_breaks (ft : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) (hN : Numbered ft d)
    (hne : ∀ lay, layTrees d.st.codes sent = some lay → lay.shapes.size ≠ 0) :
    ¬ Numbered ft d' := by
  intro hN'
  obtain ⟨_, lay, hl, S⟩ := adoptP_seat d d' sent given ids h
  have r := adoptP_roots d d' sent given ids h
  have a := hN'.1
  rw [r, hN.1, S.size] at a
  exact hne lay hl (by omega)

end VerifiableInference.Desc.Book
