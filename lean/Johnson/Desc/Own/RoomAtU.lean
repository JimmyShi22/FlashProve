--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/RoomAtU.lean: what the third of the clauses on room means: foldFits' "the folded
row's entries have room in o_u" (Johnson/Desc/Own/Lin.lean), in words of places. Theorems. No block
imports this file. Beside LinMeans.lean's omega_has_room and w_has_room.

  entries_pos    a code's message length is at least 1: the folded row takes at least one entry.
  u_has_room     foldFits' yes gives: o_u can hold a vector in its layout (roomCan); the folded
                 row's entries are at most the places of its real rows; and no place of its sample's
                 pad in the main table is among them (each holds an entry's number that is at least
                 the number of entries).
What is not claimed. That the entries lie at real PLACES of their rows: that wants the code's
message length to be a power of two (RoomPlaces.lean: room_places). Nothing on soundness.

-/
import Johnson.Desc.Own.LinMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Params

/-- The folded row takes at least one entry. -/
theorem entries_pos (S : FoldeqShape) (h : 1 ≤ S.index.code.ell) : 1 ≤ S.entries := by
  unfold FoldeqShape.entries FoldeqShape.tailFirst
  have hs : 0 < 2 ^ S.index.code.logR := Nat.two_pow_pos _
  have h1 : 0 < (S.index.code.ell + 2 ^ S.index.code.logR - 1) / 2 ^ S.index.code.logR :=
    Nat.div_pos (by omega) hs
  have h2 := Nat.mul_pos h1 hs
  simp only []
  omega

/-- foldFits' yes: the folded row's entries have room in o_u, in words of places. -/
theorem u_has_room (codes : Codes) (S : FoldeqShape) (h : foldFits codes S = true) :
    roomCan codes S.u S.rowsHigh = true ∧
    S.entries ≤ S.u.mainRows * 2 ^ (vectorLay codes S.u S.rowsHigh).placeBits ∧
    ∀ p ∈ (if S.u.answers == 0 then [] else (padMade codes S.u).getD []),
      p.part = .main → S.entries ≤ (vectorLay codes S.u S.rowsHigh).entryAt p.index := by
  obtain ⟨hs, _, hr⟩ := (foldFits_iff codes S).1 h
  exact (le_roomOf codes S.u S.rowsHigh S.entries (entries_pos S hs.1.1.2.2.1)).1 hr

end VerifiableInference.Desc.Own
