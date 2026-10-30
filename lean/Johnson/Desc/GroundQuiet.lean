-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/GroundQuiet.lean: the record of Johnson/Desc/GroundKeeps.lean WITHOUT TWO OF ITS TEN
FUNCTIONS: a relation R on statements that is reflexive, transitive, and kept by the eight plain
functions of the ground that ask nothing of their caller: a new group, the receiving and the taking
over of messages, a joining, a row, a mask's entry, the closing of a ledger, the spending of a mask.
Left out, beside the beginning of a proximity test: the admitting of a sample (admitP) and the
copying from another statement (elsewhereP): a relation that speaks of what rows MEAN is kept by
these two only under a premise on what the caller hands in. A step that calls the eight alone is
proved once for every such R. Theorems.

  GroundQuiet R        the record: eight functions.
  GroundQuiet.addRowsFrom · addRows · takeMasksInto · takeMasks   the four that are made of these.
  GroundKeeps.quiet    whoever has the ten has the eight.
What is not claimed. Nothing on admitP, elsewhereP, beginRunP. Nothing on a step that writes the
statement by another road than these functions.

-/
import Johnson.Desc.GroundKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- What a relation on statements owes: the eight functions that ask nothing of their caller. -/
structure GroundQuiet (R : Statement → Statement → Prop) : Prop where
  refl : ∀ T, R T T
  trans : ∀ {A B C}, R A B → R B C → R A C
  newGroup : ∀ {L : Type} (d d' : DState L) (code maskCode n : Nat),
    newGroupP d code maskCode = some (n, d') → R d.st d'.st
  recv : ∀ {L : Type} (ft : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat),
    recvP ft d sent = some (ids, d') → R d.st d'.st
  join : ∀ {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool),
    joinP d g o kept = some d' → R d.st d'.st
  addRow : ∀ {L : Type} (d d' : DState L) (g : Nat) (row : OnBytes.Row),
    addRowP d g row = some d' → R d.st d'.st
  takeMask : ∀ {L : Type} (d d' : DState L) (o n : Nat),
    takeMaskP d o = some (n, d') → R d.st d'.st
  closeLedger : ∀ {L : Type} (d d' : DState L) (o : Nat), closeLedgerP d o = some d' → R d.st d'.st
  spendAsMask : ∀ {L : Type} (d d' : DState L) (o : Nat), spendAsMaskP d o = some d' → R d.st d'.st
  adopt : ∀ {L : Type} (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat),
    adoptP d sent given = some (ids, d') → R d.st d'.st

variable {R : Statement → Statement → Prop} {L : Type}

/-- Rows added one behind the other keep R. -/
theorem GroundQuiet.addRowsFrom (H : GroundQuiet R) (g : Nat) (rows : List OnBytes.Row) :
    ∀ (d d' : DState L), addRowsFrom g rows d = some d' → R d.st d'.st := by
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
theorem GroundQuiet.addRows (H : GroundQuiet R) (d d' : DState L) (g : Nat)
    (rows : List OnBytes.Row) (h : addRowsP d g rows = some d') : R d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact H.addRowsFrom g rows d d' h
  · cases h

/-- Entries of a mask taken one behind the other keep R. -/
theorem GroundQuiet.takeMasksInto (H : GroundQuiet R) (o : Nat) (count : Nat) :
    ∀ (d d' : DState L) (acc : Array Nat) (r : List Nat),
      takeMasksInto o count d acc = some (r, d') → R d.st d'.st := by
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
theorem GroundQuiet.takeMasks (H : GroundQuiet R) (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : R d.st d'.st :=
  H.takeMasksInto o count d d' #[] r h

/-- Whoever has the ten has the eight. -/
theorem GroundKeeps.quiet (H : GroundKeeps R) : GroundQuiet R where
  refl := H.refl
  trans := H.trans
  newGroup := H.newGroup
  recv := H.recv
  join := H.join
  addRow := H.addRow
  takeMask := H.takeMask
  closeLedger := H.closeLedger
  spendAsMask := H.spendAsMask
  adopt := H.adopt

end VerifiableInference.Desc.Ground
