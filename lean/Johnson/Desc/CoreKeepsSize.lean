-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/CoreKeepsSize.lean: the eight plain functions of the ground that write the statement
alone (Johnson/Desc/First/Base/Ground.lean: a new group; a sample's answers; a message joins a
group; a new open row; the next free mask entry; a ledger is shut; a message becomes a mask; a
message is sampled in another statement) leave the NUMBER of the statement's oracle messages as it
is. So does the beginning of a proximity test. Statements with their proofs.

  coreStill_size   the eight, as one member of CoreStill (Johnson/Desc/CoreKeeps.lean): so every
                   walk that is typed over CoreStill carries it, alone or, by CoreStill.and, beside
                   "the book and the count of roots stay" (coreStill_same).
  coreStill_three  the two together.
  ‹x›P_size        the eight by name, for a caller that walks no CoreStill.
  beginRunP_size   the ninth: not among CoreStill's eight.
The two functions that bring messages in (recvP, adoptP) raise the number: not here.

What is not claimed. Nothing on which messages these are beyond their number. Nothing on soundness.

-/
import Johnson.Desc.CoreKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

variable {L : Type}

/-- **The eight leave the number of oracle messages as it is.** -/
theorem coreStill_size : CoreStill fun a b => b.st.oracles.size = a.st.oracles.size where
  refl := fun _ => rfl
  trans := fun a b => b.trans a
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [coreOf, withGroup]
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, -, places, -, rfl⟩ := h
      simp [coreOf, admitted]
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [coreOf, withMessageInGroup]
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [coreOf, withRow]
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold takeMaskP at h
    split at h
    · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl : _ = d' := congrArg Prod.snd e
      simp [coreOf]
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [coreOf, closeLedgers]
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [coreOf]
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [coreOf]
    · cases h

/-- The number of messages, the book of trees and the count of roots: all three stay. -/
theorem coreStill_three : CoreStill fun a b =>
    b.st.oracles.size = a.st.oracles.size ∧ (b.book = a.book ∧ b.roots = a.roots) :=
  coreStill_size.and coreStill_same

theorem newGroupP_size (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.newGroup d d' code maskCode n h

theorem admitP_size (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.admit d d' o rows h

theorem joinP_size (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.join d d' g o kept h

theorem addRowP_size (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.addRow d d' g row h

theorem addRowsP_size (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.addRows d d' g rows h

theorem takeMaskP_size (d d' : DState L) (o n : Nat)
    (h : takeMaskP d o = some (n, d')) : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.takeMask d d' o n h

theorem takeMasksP_size (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.takeMasks d d' o count r h

theorem closeLedgerP_size (d d' : DState L) (o : Nat)
    (h : closeLedgerP d o = some d') : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.closeLedger d d' o h

theorem spendAsMaskP_size (d d' : DState L) (o : Nat)
    (h : spendAsMaskP d o = some d') : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.spendAsMask d d' o h

theorem elsewhereP_size (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : d'.st.oracles.size = d.st.oracles.size :=
  coreStill_size.elsewhere d d' mine other theirs h

/-- Shutting ledgers leaves the number. -/
theorem closeLedgers_size' : ∀ (l : List Nat) (S : Statement),
    (closeLedgers S l).oracles.size = S.oracles.size
  | [], _ => rfl
  | _ :: l, _ => (closeLedgers_size' l _).trans (by simp)

/-- **The beginning of a proximity test leaves the number too.** -/
theorem beginRunP_size (d d' : DState L) (g : Nat) (x : RunInput)
    (h : beginRunP d g = some (x, d')) : d'.st.oracles.size = d.st.oracles.size := by
  unfold beginRunP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨G, -, -, rfl⟩ := h
    exact closeLedgers_size' _ _
  · cases h

end VerifiableInference.Desc.Ground
