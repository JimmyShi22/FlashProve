-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.WordsThm
/-!
# Small facts on Hash.lean

Where blake2b returns no bytes, and what it returns elsewhere. The ties to the plain definition of
Run/Blake2b/Spec.lean are in SpecThm.lean.
-/
namespace Run.Blake2b

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

/-- Inside the range of lengths blake2b is the first outlen bytes of the last state's chaining
value. -/
theorem blake2b_inside (key data : ByteArray) (outlen : Nat) (h1 : 1 ≤ outlen)
    (h64 : outlen ≤ 64) (hk : key.size ≤ 64) :
    blake2b key data outlen = (state key data outlen).h.bytes outlen := by
  unfold blake2b
  rw [if_neg (by omega), if_neg (by omega)]

/-- Outside that range the function returns no bytes. -/
theorem blake2b_outside (key data : ByteArray) (outlen : Nat)
    (h : ¬ (1 ≤ outlen ∧ outlen ≤ 64 ∧ key.size ≤ 64)) :
    blake2b key data outlen = ByteArray.empty := by
  unfold blake2b
  split
  · rfl
  · split
    · rfl
    · exact absurd ⟨by omega, by omega, by omega⟩ h

end Run.Blake2b
