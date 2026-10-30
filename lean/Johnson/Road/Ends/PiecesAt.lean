-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/PiecesAt.lean

A vector that is laid in pieces (Cb/Pv/Lookup/Ends/Pieces.lean: pwVec), at a place of one of its
pieces.

Main theorems:
* "pwVec_mem": a vector laid in pieces that are pairwise apart holds, at a place X of a piece p of
  the list, key number X - off of p.
* "block_of": the block of 2^l places that holds Y.


-/
import Cb.Pv.Lookup.Ends.Pieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

variable {E : Type} [Field E] {ι : Type} (off b : ι → ℕ)

/-- **The vector at a place of one of its pieces.** -/
theorem pwVec_mem (key : ι → ℕ → E) (pad : E) (ps : List ι)
    (hD : ps.Pairwise fun p q => off p + 2 ^ b p ≤ off q ∨ off q + 2 ^ b q ≤ off p) (p : ι)
    (hp : p ∈ ps) (X : ℕ) (hX : off p ≤ X ∧ X < off p + 2 ^ b p) :
    pwVec off b key pad ps X = key p (X - off p) := by
  induction ps with
  | nil => exact absurd hp (List.not_mem_nil)
  | cons q ps ih =>
    obtain ⟨hq, hps⟩ := List.pairwise_cons.1 hD
    show (if off q ≤ X ∧ X < off q + 2 ^ b q then key q (X - off q)
      else pwVec off b key pad ps X) = _
    rcases List.mem_cons.1 hp with rfl | hp'
    · rw [if_pos hX]
    · have hn : ¬(off q ≤ X ∧ X < off q + 2 ^ b q) := by
        intro hq'
        rcases hq p hp' with h | h <;> omega
      rw [if_neg hn]
      exact ih hps hp'

/-- The block of 2^l places that holds Y. -/
theorem block_of (Y l : ℕ) :
    Y / 2 ^ l * 2 ^ l ≤ Y ∧ Y < Y / 2 ^ l * 2 ^ l + 2 ^ l ∧ Y - Y / 2 ^ l * 2 ^ l = Y % 2 ^ l := by
  have hp : 0 < 2 ^ l := Nat.pos_of_ne_zero (by positivity)
  have h1 := Nat.div_add_mod Y (2 ^ l)
  have h2 := Nat.mod_lt Y hp
  rw [Nat.mul_comm] at h1
  omega

end OnBytes.Ends

#print axioms OnBytes.Ends.pwVec_mem
