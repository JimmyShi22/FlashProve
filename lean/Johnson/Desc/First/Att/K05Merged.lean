-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Merged.lean: the last coordinates of an array (lastCoords,
Att/TablesP.lean): five small facts.

Main names:
  `lastCoords_size`, `last_last` (the last n of the last b are the last n), `last_append` (the last
    n of a ++ b are b's), `inner_last` (a unit's inner
  point is the key point's last coordinates), `extract_glue` (two cuts side by side).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.TablesP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes

theorem lastCoords_size {z : Array E} {n : Nat} (h : n ≤ z.size) : (lastCoords z n).size = n := by
  unfold lastCoords
  rw [Array.size_extract]
  omega

theorem last_last {z : Array E} {b n : Nat} (h1 : n ≤ b) (h2 : b ≤ z.size) :
    lastCoords (lastCoords z b) n = lastCoords z n := by
  have hs := lastCoords_size h2
  unfold lastCoords at hs ⊢
  rw [hs, Array.extract_extract]
  congr 1 <;> omega

theorem last_append (a : Array E) {b : Array E} {n : Nat} (h : n ≤ b.size) : lastCoords (a ++ b) n = lastCoords b n := by
  unfold lastCoords
  rw [Array.extract_append, Array.size_append]
  have e1 : a.extract (a.size + b.size - n) (a.size + b.size) = #[] := by
    apply Array.extract_empty_of_size_le_start
    omega
  rw [e1, Array.empty_append]
  congr 1 <;> omega

theorem inner_last (u : UnitG) (zk : Array E) : inner u zk = lastCoords zk u.bits := rfl

/-- two cuts side by side -/
theorem extract_glue (z : Array E) {i j k : Nat} (h1 : i ≤ j) (h2 : j ≤ k) : z.extract i j ++ z.extract j k = z.extract i k := by
  rw [Array.extract_append_extract]
  congr 1 <;> omega

end VerifiableInference.Desc.First.Att.P
