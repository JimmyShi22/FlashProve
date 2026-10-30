-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/Join.lean: the verifier's table SILU, at the stored example's numbers, as the
list of the library's stored words: `silu_list`, `silu_size`. From `Meaning.Gate.silu_get` and
`silu_word` (Johnson/Meaning/GateRows.lean), which pay the table's arithmetic entry by entry.

-/
import Johnson.Unfolds.Silu.Def
import Johnson.Meaning.GateRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Silu
open OnBytes.Model.Layer

theorem siluWord_stored {t : Nat} (ht : t < 65536) :
    siluWord 8 4095 (expPowers 8 32768) t = siluW t := by
  have h1 := Meaning.Gate.silu_get true true ht
  have h2 := Meaning.Gate.silu_word true true ht
  rw [h1] at h2
  unfold siluW
  rw [← h2, Int.toNat_natCast]

theorem silu_list (p3 gcl : Bool) :
    (gateTables 8 4095 p3 gcl).1.toList = fromTo siluW 0 65536 := by
  unfold gateTables
  dsimp only
  rw [if_pos (show ((8 : Nat) == 8) = true from rfl)]
  exact toList_of_range_map _ siluW 65536 fun _ ht => siluWord_stored ht

theorem silu_size (p3 gcl : Bool) : (gateTables 8 4095 p3 gcl).1.size = 65536 := by
  rw [← Array.length_toList, silu_list, length_fromTo]

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.siluWord_stored
#print axioms Johnson.Unfolds.Silu.silu_list
#print axioms Johnson.Unfolds.Silu.silu_size
