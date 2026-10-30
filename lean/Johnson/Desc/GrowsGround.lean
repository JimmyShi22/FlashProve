-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/GrowsGround.lean: none of the plain functions by which a step of the description
changes the statement drops a group or an oracle message, changes its number, or takes back a mark
(sampled; inRun): wherever such a function returns, the statement behind has grown out of the one in
front (Johnson/Desc/Grows.lean). One theorem for each function. Theorems.

  newGroupP · recvP · admitP · joinP · addRowP · addRowsFrom · addRowsP · takeMaskP ·
  takeMasksInto · takeMasksP · closeLedgerP · spendAsMaskP · beginRunP · adoptP · elsewhereP: each
  name with _grows behind it.
No proof reads a function's test: the theorems hold whatever the named clauses ask.
What is not claimed: as in Johnson/Desc/Grows.lean: NOTHING ON ROWS. Nothing on a step that writes
the statement by another road than these functions.

-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

variable {L : Type}

/-- A new group. -/
theorem newGroupP_grows (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : Grows d.st d'.st := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact grows_withGroup d.st code maskCode
  · cases h

/-- Messages are received. -/
theorem recvP_grows (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) : Grows d.st d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact grows_stSent d.st sent
  · cases h

/-- A message's sample is admitted. -/
theorem admitP_grows (d d' : DState L) (o : Nat) (rows : Array Row)
    (h : admitP d o rows = some d') : Grows d.st d'.st := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, -, places, -, rfl⟩ := h
    exact grows_admitted d.st o x.shape places rows
  · cases h

/-- A message joins a group. -/
theorem joinP_grows (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : Grows d.st d'.st := by
  unfold joinP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      subst h
      exact grows_joined d.st g o kept G
  · cases h

/-- A row is added to a group. -/
theorem addRowP_grows (d d' : DState L) (g : Nat) (row : Row)
    (h : addRowP d g row = some d') : Grows d.st d'.st := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact grows_withRow d.st g row
  · cases h

/-- Rows are added, one behind the other. -/
theorem addRowsFrom_grows (g : Nat) (rows : List Row) : ∀ (d d' : DState L),
    addRowsFrom g rows d = some d' → Grows d.st d'.st := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact Grows.refl _
  | cons row l ih =>
    intro d d' h
    simp only [addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact (addRowP_grows d e g row h1).trans (ih e d' h)

/-- Rows are added to a group. -/
theorem addRowsP_grows (d d' : DState L) (g : Nat) (rows : List Row)
    (h : addRowsP d g rows = some d') : Grows d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_grows g rows d d' h
  · cases h

/-- An entry of a mask is taken. -/
theorem takeMaskP_grows (d d' : DState L) (o n : Nat)
    (h : takeMaskP d o = some (n, d')) : Grows d.st d'.st := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact grows_modOracle d.st o _ fun _ => ⟨rfl, id, fun _ k => k⟩
  · cases h

/-- Entries of a mask are taken, one behind the other. -/
theorem takeMasksInto_grows (o : Nat) (count : Nat) : ∀ (d d' : DState L) (acc : Array Nat)
    (r : List Nat), takeMasksInto o count d acc = some (r, d') → Grows d.st d'.st := by
  induction count with
  | zero =>
    intro d d' acc r h
    simp only [takeMasksInto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Grows.refl _
  | succ n ih =>
    intro d d' acc r h
    simp only [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e h1
      exact (takeMaskP_grows d e o i h1).trans (ih e d' _ r h)

/-- So many entries of a mask are taken. -/
theorem takeMasksP_grows (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : Grows d.st d'.st :=
  takeMasksInto_grows o count d d' #[] r h

/-- A ledger of mask entries is closed. -/
theorem closeLedgerP_grows (d d' : DState L) (o : Nat)
    (h : closeLedgerP d o = some d') : Grows d.st d'.st := by
  unfold closeLedgerP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact grows_closeLedgers [o] d.st
  · cases h

/-- A message is spent as a mask. -/
theorem spendAsMaskP_grows (d d' : DState L) (o : Nat)
    (h : spendAsMaskP d o = some d') : Grows d.st d'.st := by
  unfold spendAsMaskP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact grows_modOracle d.st o _ fun _ => ⟨rfl, id, fun _ k => k⟩
  · cases h

/-- A proximity test begins: the mark is laid, never taken back. -/
theorem beginRunP_grows (d d' : DState L) (g : Nat) (r : RunInput)
    (h : beginRunP d g = some (r, d')) : Grows d.st d'.st := by
  unfold beginRunP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    first
      | (obtain ⟨G, -, lay, -, -, rfl⟩ := h
         exact grows_begun d.st g G)
      | (obtain ⟨G, -, -, rfl⟩ := h
         exact grows_begun d.st g G)
  · cases h

/-- A message of another chain is taken over. -/
theorem adoptP_grows (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) : Grows d.st d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact grows_stSent d.st sent
  · cases h

/-- A message is marked as sampled on another chain. -/
theorem elsewhereP_grows (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : Grows d.st d'.st := by
  unfold elsewhereP at h
  split at h
  · cases hy : other.oracles[theirs]? with
    | none => simp [hy] at h
    | some y =>
      simp only [hy, Option.map_some, Option.some.injEq] at h
      subst h
      exact grows_modOracle d.st mine _ fun _ => ⟨rfl, fun _ => rfl, fun _ k => k⟩
  · cases h

end VerifiableInference.Desc.Ground
