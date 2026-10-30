-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/CoreKeeps.lean: Johnson/Desc/GroundKeeps.lean once more, for a relation that reads
MORE OF THE RECORD THAN THE STATEMENT: the statement, THE BOOK OF TREES AND THE COUNT OF ROOTS
(Core). What such a relation R owes so that every step which writes these three through the ground's
plain functions keeps it: R is reflexive and transitive, and each of these functions, but for the
beginning of a proximity test, keeps it. A kind's step is then proved once, for every such R.
Definitions and theorems.

  Core, coreOf         the three, and how they are read off a carried state.
  CoreStill R          what is owed at the eight functions that write the statement alone.
  CoreRecv ft R        these eight and the receiving AT ONE ft, the number of the chain's first
                       tree: for a relation that is true at the chain's own ft alone (a tree's
                       number in the book), on a chain that takes no tree over.

  CoreKeeps R          all ten: the eight, the receiving at every ft, the taking over.
  CoreKeeps.at         whoever has the ten has the nine at each ft.
  beginRun_same        the beginning of a proximity test leaves the book and the roots too.
  CoreStill.addRowsFrom · addRows · takeMasksInto · takeMasks   the four that are made of the eight.
  CoreStill.and, CoreRecv.and, CoreKeeps.and   two such relations together are one.
  coreStill_same       THE EIGHT LEAVE THE BOOK AND THE ROOTS AS THEY ARE. (The
                       like stands, function by function, in Johnson/Desc/Book/BookFitsGround.lean
                       and BookNumbers.lean; said here once more, as one member, so that this file
                       stands on the ground alone.)
  CoreStill.ofBook, CoreKeeps.ofBook   a relation on books, read at Core.book: it owes the receiving
                       and the taking over alone.
  CoreKeeps.ofSt       a relation on statements that meets GroundKeeps meets it, read at Core.st.
  ByC R core           the relation on records: R at the three that core reads.
What is not claimed. beginRunP is left out of the records, as in GroundKeeps. Which relations are
such: see Johnson/Desc/CoreKeepsBook.lean [not in this library]. Nothing on a step that writes one
of the three by another road than these functions: a record that is copied into another, a reading
that counts an opening.

-/
import Johnson.Desc.GroundKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- What of a carried state the ground's plain functions write, but for the opened columns. -/
structure Core where
  st : Statement
  book : TreeBook
  roots : Nat

/-- The three, off a carried state. -/
def coreOf {L : Type} (d : DState L) : Core := ⟨d.st, d.book, d.roots⟩

/-- What a relation on the three owes at the eight functions that write the statement alone. -/
structure CoreStill (R : Core → Core → Prop) : Prop where
  refl : ∀ T, R T T
  trans : ∀ {A B C}, R A B → R B C → R A C
  newGroup : ∀ {L : Type} (d d' : DState L) (code maskCode n : Nat),
    newGroupP d code maskCode = some (n, d') → R (coreOf d) (coreOf d')
  admit : ∀ {L : Type} (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row),
    admitP d o rows = some d' → R (coreOf d) (coreOf d')
  join : ∀ {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool),
    joinP d g o kept = some d' → R (coreOf d) (coreOf d')
  addRow : ∀ {L : Type} (d d' : DState L) (g : Nat) (row : OnBytes.Row),
    addRowP d g row = some d' → R (coreOf d) (coreOf d')
  takeMask : ∀ {L : Type} (d d' : DState L) (o n : Nat),
    takeMaskP d o = some (n, d') → R (coreOf d) (coreOf d')
  closeLedger : ∀ {L : Type} (d d' : DState L) (o : Nat),
    closeLedgerP d o = some d' → R (coreOf d) (coreOf d')
  spendAsMask : ∀ {L : Type} (d d' : DState L) (o : Nat),
    spendAsMaskP d o = some d' → R (coreOf d) (coreOf d')
  elsewhere : ∀ {L : Type} (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat),
    elsewhereP d mine other theirs = some d' → R (coreOf d) (coreOf d')

/-- What a relation on the three owes ON A CHAIN THAT RECEIVES ALL ITS TREES: the eight, and the
receiving AT THE CHAIN's OWN NUMBER OF ITS FIRST TREE, ft. -/
structure CoreRecv (ft : Nat) (R : Core → Core → Prop) : Prop extends CoreStill R where
  recv : ∀ {L : Type} (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat),
    recvP ft d sent = some (ids, d') → R (coreOf d) (coreOf d')

/-- What a relation on the three owes at all ten: the eight, the receiving at every ft, and the
taking over. -/
structure CoreKeeps (R : Core → Core → Prop) : Prop extends CoreStill R where
  recv : ∀ {L : Type} (ft : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat),
    recvP ft d sent = some (ids, d') → R (coreOf d) (coreOf d')
  adopt : ∀ {L : Type} (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat),
    adoptP d sent given = some (ids, d') → R (coreOf d) (coreOf d')

variable {R : Core → Core → Prop} {L : Type}

/-- Rows added one behind the other keep R. -/
theorem CoreStill.addRowsFrom (H : CoreStill R) (g : Nat) (rows : List OnBytes.Row) :
    ∀ (d d' : DState L), addRowsFrom g rows d = some d' → R (coreOf d) (coreOf d') := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [Ground.addRowsFrom, Option.some.injEq] at h
    subst h
    exact H.refl _
  | cons row l ih =>
    intro d d' h
    simp only [Ground.addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact H.trans (H.addRow d e g row h1) (ih e d' h)

/-- Rows added to a group keep R. -/
theorem CoreStill.addRows (H : CoreStill R) (d d' : DState L) (g : Nat)
    (rows : List OnBytes.Row) (h : addRowsP d g rows = some d') : R (coreOf d) (coreOf d') := by
  unfold addRowsP at h
  split at h
  · exact H.addRowsFrom g rows d d' h
  · cases h

/-- Entries of a mask taken one behind the other keep R. -/
theorem CoreStill.takeMasksInto (H : CoreStill R) (o : Nat) (count : Nat) :
    ∀ (d d' : DState L) (acc : Array Nat) (r : List Nat),
      takeMasksInto o count d acc = some (r, d') → R (coreOf d) (coreOf d') := by
  induction count with
  | zero =>
    intro d d' acc r h
    simp only [Ground.takeMasksInto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact H.refl _
  | succ n ih =>
    intro d d' acc r h
    simp only [Ground.takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e h1
      exact H.trans (H.takeMask d e o i h1) (ih e d' _ r h)

/-- So many entries of a mask taken keep R. -/
theorem CoreStill.takeMasks (H : CoreStill R) (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : R (coreOf d) (coreOf d') :=
  H.takeMasksInto o count d d' #[] r h

/-- Two relations that the eight keep, together. -/
theorem CoreStill.and {R' : Core → Core → Prop} (H : CoreStill R)
    (K : CoreStill R') : CoreStill fun a b => R a b ∧ R' a b where
  refl := fun T => ⟨H.refl T, K.refl T⟩
  trans := fun a b => ⟨H.trans a.1 b.1, K.trans a.2 b.2⟩
  newGroup := fun d d' c m n h => ⟨H.newGroup d d' c m n h, K.newGroup d d' c m n h⟩
  admit := fun d d' o r h => ⟨H.admit d d' o r h, K.admit d d' o r h⟩
  join := fun d d' g o k h => ⟨H.join d d' g o k h, K.join d d' g o k h⟩
  addRow := fun d d' g r h => ⟨H.addRow d d' g r h, K.addRow d d' g r h⟩
  takeMask := fun d d' o n h => ⟨H.takeMask d d' o n h, K.takeMask d d' o n h⟩
  closeLedger := fun d d' o h => ⟨H.closeLedger d d' o h, K.closeLedger d d' o h⟩
  spendAsMask := fun d d' o h => ⟨H.spendAsMask d d' o h, K.spendAsMask d d' o h⟩
  elsewhere := fun d d' m o t h => ⟨H.elsewhere d d' m o t h, K.elsewhere d d' m o t h⟩

/-- **The eight leave the book of trees and the count of roots as they are.** -/
theorem coreStill_same : CoreStill fun a b => b.book = a.book ∧ b.roots = a.roots where
  refl := fun _ => ⟨rfl, rfl⟩
  trans := fun a b => ⟨b.1.trans a.1, b.2.trans a.2⟩
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, -, places, -, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨rfl, rfl⟩
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold takeMaskP at h
    split at h
    · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl : _ = d' := congrArg Prod.snd e
      exact ⟨rfl, rfl⟩
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨rfl, rfl⟩
    · cases h

/-- A state with the book and the roots of another: its three, written out. -/
theorem core_eq (d d' : DState L) (hb : d'.book = d.book) (hr : d'.roots = d.roots) :
    (⟨d'.st, (coreOf d).book, (coreOf d).roots⟩ : Core) = coreOf d' := by
  unfold coreOf
  rw [hb, hr]

/-- **The beginning of a proximity test**, which the records leave out, leaves the book and the
roots too. -/
theorem beginRun_same (d d' : DState L) (g : Nat) (inp : RunInput)
    (h : beginRunP d g = some (inp, d')) : d'.book = d.book ∧ d'.roots = d.roots := by
  unfold beginRunP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨G, -, -, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · cases h

/-- Whoever has all ten has the nine at each ft. -/
theorem CoreKeeps.at (H : CoreKeeps R) (ft : Nat) : CoreRecv ft R :=
  { H.toCoreStill with recv := fun d d' s i h => H.recv ft d d' s i h }

/-- Two relations that the nine keep, together. -/
theorem CoreRecv.and {ft : Nat} {R' : Core → Core → Prop} (H : CoreRecv ft R)
    (K : CoreRecv ft R') : CoreRecv ft fun a b => R a b ∧ R' a b :=
  { H.toCoreStill.and K.toCoreStill with
    recv := fun d d' s i h => ⟨H.recv d d' s i h, K.recv d d' s i h⟩ }

/-- Two such relations together are one. -/
theorem CoreKeeps.and {R' : Core → Core → Prop} (H : CoreKeeps R)
    (K : CoreKeeps R') : CoreKeeps fun a b => R a b ∧ R' a b where
  refl := fun T => ⟨H.refl T, K.refl T⟩
  trans := fun a b => ⟨H.trans a.1 b.1, K.trans a.2 b.2⟩
  newGroup := fun d d' c m n h => ⟨H.newGroup d d' c m n h, K.newGroup d d' c m n h⟩
  recv := fun f d d' s i h => ⟨H.recv f d d' s i h, K.recv f d d' s i h⟩
  admit := fun d d' o r h => ⟨H.admit d d' o r h, K.admit d d' o r h⟩
  join := fun d d' g o k h => ⟨H.join d d' g o k h, K.join d d' g o k h⟩
  addRow := fun d d' g r h => ⟨H.addRow d d' g r h, K.addRow d d' g r h⟩
  takeMask := fun d d' o n h => ⟨H.takeMask d d' o n h, K.takeMask d d' o n h⟩
  closeLedger := fun d d' o h => ⟨H.closeLedger d d' o h, K.closeLedger d d' o h⟩
  spendAsMask := fun d d' o h => ⟨H.spendAsMask d d' o h, K.spendAsMask d d' o h⟩
  adopt := fun d d' s g i h => ⟨H.adopt d d' s g i h, K.adopt d d' s g i h⟩
  elsewhere := fun d d' m o t h => ⟨H.elsewhere d d' m o t h, K.elsewhere d d' m o t h⟩

/-- A relation on statements that the ground's functions keep, read at the statement. -/
theorem CoreKeeps.ofSt {Q : Statement → Statement → Prop} (H : GroundKeeps Q) :
    CoreKeeps fun a b => Q a.st b.st where
  refl := fun T => H.refl T.st
  trans := fun a b => H.trans a b
  newGroup := fun d d' c m n h => H.newGroup d d' c m n h
  recv := fun f d d' s i h => H.recv f d d' s i h
  admit := fun d d' o r h => H.admit d d' o r h
  join := fun d d' g o k h => H.join d d' g o k h
  addRow := fun d d' g r h => H.addRow d d' g r h
  takeMask := fun d d' o n h => H.takeMask d d' o n h
  closeLedger := fun d d' o h => H.closeLedger d d' o h
  spendAsMask := fun d d' o h => H.spendAsMask d d' o h
  adopt := fun d d' s g i h => H.adopt d d' s g i h
  elsewhere := fun d d' m o t h => H.elsewhere d d' m o t h

/-- A relation on books, read at the book: the eight keep it, for they leave the book. -/
theorem CoreStill.ofBook {Q : TreeBook → TreeBook → Prop} (hr : ∀ B, Q B B)
    (ht : ∀ {A B C}, Q A B → Q B C → Q A C) : CoreStill fun a b => Q a.book b.book := by
  have key : ∀ a b : Core, (b.book = a.book ∧ b.roots = a.roots) → Q a.book b.book :=
    fun a b e => by
      rw [e.1]
      exact hr _
  exact
    { refl := fun T => hr T.book
      trans := fun a b => ht a b
      newGroup := fun d d' c m n h => key _ _ (coreStill_same.newGroup d d' c m n h)
      admit := fun d d' o r h => key _ _ (coreStill_same.admit d d' o r h)
      join := fun d d' g o k h => key _ _ (coreStill_same.join d d' g o k h)
      addRow := fun d d' g r h => key _ _ (coreStill_same.addRow d d' g r h)
      takeMask := fun d d' o n h => key _ _ (coreStill_same.takeMask d d' o n h)
      closeLedger := fun d d' o h => key _ _ (coreStill_same.closeLedger d d' o h)
      spendAsMask := fun d d' o h => key _ _ (coreStill_same.spendAsMask d d' o h)
      elsewhere := fun d d' m o t h => key _ _ (coreStill_same.elsewhere d d' m o t h) }

/-- **A relation on books that the receiving and the taking over keep is kept by all ten.** -/
theorem CoreKeeps.ofBook {Q : TreeBook → TreeBook → Prop} (hr : ∀ B, Q B B)
    (ht : ∀ {A B C}, Q A B → Q B C → Q A C)
    (hrecv : ∀ {L : Type} (ft : Nat) (d d' : DState L) (sent : Array OracleNotice)
      (ids : Array Nat), recvP ft d sent = some (ids, d') → Q d.book d'.book)
    (hadopt : ∀ {L : Type} (d d' : DState L) (sent : Array OracleNotice)
      (given : Array (Nat × Fmt.Src)) (ids : Array Nat),
      adoptP d sent given = some (ids, d') → Q d.book d'.book) :
    CoreKeeps fun a b => Q a.book b.book :=
  { CoreStill.ofBook hr ht with
    recv := fun f d d' s i h => hrecv f d d' s i h
    adopt := fun d d' s g i h => hadopt d d' s g i h }

/-- The relation on records: R at the three that core reads. -/
def ByC {S : Type} (R : Core → Core → Prop) (core : S → Core) : S → S → Prop :=
  fun s s' => R (core s) (core s')

theorem CoreStill.by_refl {S : Type} (H : CoreStill R) (core : S → Core) (s : S) :
    ByC R core s s := H.refl _

theorem CoreStill.by_trans {S : Type} (H : CoreStill R) (core : S → Core) (a b c : S)
    (h : ByC R core a b) (k : ByC R core b c) : ByC R core a c := H.trans h k

end VerifiableInference.Desc.Ground
