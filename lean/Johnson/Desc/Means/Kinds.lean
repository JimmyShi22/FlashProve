-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Kinds.lean: every plain function on the statement keeps that no open row is
marked as a sample row.

OpenKinds (Johnson/Desc/Means/Holds.lean) is what lets a proximity test take in every open row. The
adding of a row keeps it by its own clause (addRowP_kinds). This file shows it of the other plain
functions of Johnson/Desc/First/Base/Ground.lean.

Main theorems: addRowsP_kinds, joinP_kinds, newGroupP_kinds, recvP_kinds, adoptP_kinds,
admitP_kinds, takeMaskP_kinds, closeLedgerP_kinds, spendAsMaskP_kinds, elsewhereP_kinds,
beginRunP_kinds.

What is not claimed. That a block changes the statement by these functions alone.

-/
import Johnson.Desc.Means.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open VerifiableInference.Desc.Ground Desc.Plain

variable {Lc : Type}

theorem addRowsFrom_kinds (g : Nat) : ∀ (l : List Row) (d d' : DState Lc),
    addRowsFrom g l d = some d' → OpenKinds d.st → OpenKinds d'.st
  | [], d, d', h, hK => by
    obtain rfl := Option.some.inj h
    exact hK
  | row :: l, d, d', h, hK => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFrom_kinds g l d1 d' h2 (addRowP_kinds h1 hK)

theorem addRowsP_kinds {d d' : DState Lc} {g : Nat} {rows : List Row}
    (h : addRowsP d g rows = some d') (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_kinds g rows d d' h hK
  · cases h

theorem joinP_kinds {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hK.withMessageInGroup g o kept G
  · cases h

theorem newGroupP_kinds {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    exact hK.withGroup a b
  · cases h

theorem recvP_kinds {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hK.sameGroups rfl
  · cases h

theorem adoptP_kinds {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hK.sameGroups rfl
  · cases h

theorem admitP_kinds {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    exact hK.sameGroups rfl
  · cases h

theorem takeMaskP_kinds {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hK.sameGroups rfl
  · cases h

theorem closeLedgerP_kinds {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hK.sameGroups (closeLedgers_groups [o] d.st)
  · cases h

theorem spendAsMaskP_kinds {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hK.sameGroups rfl
  · cases h

theorem elsewhereP_kinds {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hK.sameGroups rfl
  · cases h

theorem beginRunP_kinds {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hK : OpenKinds d.st) : OpenKinds d'.st := by
  obtain ⟨G, _, _, e⟩ := beginRunP_inv h
  rw [e]
  exact hK.begun g G

end OnBytes.Means
