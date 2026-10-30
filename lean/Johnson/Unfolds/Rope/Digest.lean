-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/Digest.lean: **the digest of the verifier's rotary table, at the stored
example's numbers (cs 12, theta0 500000, dh 128, lt 10), is 32 written bytes**: `rope_digest`:
`secondHashFunction 72` of the bytes that `tableHeld` and `tableHeldO` make of `ropeTable 12 500000 128 10` is
`D` (States.lean).
How. As Johnson/Unfolds/Silu/Digest.lean: `tableDigest_list`; `rope_list`: the table is the
library's stored words (from `Meaning.Rope.table_words`, Johnson/Goal/Meaning/RopeScope.lean, and
the table's size, from `Meaning.Rope.pairs_spec`, Johnson/Meaning/RopeSpec.lean); the chain in
sixteen pieces by Lean's kernel (Chain.lean).
  `toList_of_getD`: an array of n entries whose entries are f's is `fromTo f 0 n`.
Limits. At these numbers alone. That the stored full-size files give them, and that `D` is what the
parameter file's words `trope` spell, is not said here.

-/
import Johnson.Unfolds.Rope.Chain
import Johnson.Goal.Meaning.RopeScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Rope
open OnBytes.Model.Layer

/-- An array of n entries whose entries are f's, as a list. -/
theorem toList_of_getD (a : Array Nat) (f : Nat → Nat) (n : Nat) (hs : a.size = n)
    (h : ∀ j, j < n → a.getD j 0 = f j) : a.toList = fromTo f 0 n := by
  have e : a = (Array.range n).map f := by
    apply Array.ext
    · simp [hs]
    · intro i h1 _
      have := h i (hs ▸ h1)
      simp only [Array.getElem_map, Array.getElem_range]
      rw [← this]
      simp [Array.getD, h1]
  rw [e]
  exact toList_of_range_map f f n fun _ _ => rfl

/-- The rotary table's size, general in its numbers. -/
theorem size_ropeTable (cs theta0 dh lt : Nat) :
    (ropeTable cs theta0 dh lt).size = 2 * 2 ^ lt * (dh / 2) := by
  have e : ropeTable cs theta0 dh lt = ropePairs cs (2 ^ lt) (dh / 2)
      (Meaning.Rope.uOf theta0 (dh / 2)) (dh / 2) 0 fxOne
      (Array.replicate (2 * 2 ^ lt * (dh / 2)) 0) := rfl
  rw [e]
  exact (Meaning.Rope.pairs_spec cs (2 ^ lt) (dh / 2) (Meaning.Rope.uOf theta0 (dh / 2)) (dh / 2) 0
    fxOne (Array.replicate (2 * 2 ^ lt * (dh / 2)) 0) (by simp) (by omega)).1

theorem rope_size : (ropeTable 12 500000 128 10).size = 131072 := by
  rw [size_ropeTable]
  decide

theorem rope_get {j : Nat} (hj : j < 131072) : (ropeTable 12 500000 128 10).getD j 0 = ropeW j := by
  unfold ropeW
  by_cases h : j < 65536
  · have y := (Meaning.Rope.table_words (t := j / 64) (i := j % 64) (by omega)
      (Nat.mod_lt _ (by omega))).1
    rw [if_pos h]
    rw [show j / 64 * 64 + j % 64 = j by omega, show 64 * (j / 64) + j % 64 = j by omega] at y
    exact y
  · have y := (Meaning.Rope.table_words (t := (j - 65536) / 64) (i := (j - 65536) % 64) (by omega)
      (Nat.mod_lt _ (by omega))).2
    rw [if_neg h]
    rw [show (1024 + (j - 65536) / 64) * 64 + (j - 65536) % 64 = j by omega,
      show 64 * ((j - 65536) / 64) + (j - 65536) % 64 = j - 65536 by omega] at y
    exact y

theorem rope_list : (ropeTable 12 500000 128 10).toList = fromTo ropeW 0 131072 :=
  toList_of_getD _ ropeW 131072 rope_size fun _ hj => rope_get hj

/-- **THE DIGEST OF THE ROTARY TABLE.** -/
theorem rope_digest :
    OnBytes.secondHashFunction 72 ((ropeTable 12 500000 128 10).foldl
                  (fun b x => b ++ OnBytes.word32 x) ByteArray.empty) = D := by
  rw [tableDigest_list, rope_size, rope_list, digestL]

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.toList_of_getD
#print axioms Johnson.Unfolds.Rope.size_ropeTable
#print axioms Johnson.Unfolds.Rope.rope_size
#print axioms Johnson.Unfolds.Rope.rope_get
#print axioms Johnson.Unfolds.Rope.rope_list
#print axioms Johnson.Unfolds.Rope.rope_digest
