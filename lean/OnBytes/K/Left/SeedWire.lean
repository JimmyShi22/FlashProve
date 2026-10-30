-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/SeedWire.lean: the seed of a table's record, read off K digests by the record's wire,
is the program's own drawing on these digests' bytes.

"The program" is the Lean program `verify-on-bytes` (OnBytes/Main.lean). It draws the seeds of a
table's record by `recordSeeds` (OnBytes/Entry/Table.lean) from the blocks of one round of a chain
of its own. OnBytes/K/SeedBytes.lean has these draws as a function of K digests: `seedsOfDigs`. The
wire of a record (`recSeedK`, OnBytes/Flat/RecordSeed.lean) draws a seed from the first blocks of K
digests. The tie of the seeds' two tests of the entry's arm (Johnson/Top/TieSeedArm.lean) asks that
the two agree (`wire`) and that the blocks fit (`room`). Here both are shown, for every code, every
number of coordinates and of seeds, and every K with room.

Main theorems.
 `ofFn_eq_range`   the first b of K digests as an array of byte strings, written in two ways.
 `wire_recSeedK`   `recSeedK T lg s K h a = seedOfC lg s (seedsOfDigs .two lg s a)`, for every a.
 `room_recSeedK`   what `recSeedK` asks of K, (seedBS lg s).b ≤ K, is `nBlocks lg s ≤ K`.

What is not claimed. That any oracle functions answer a typed query with the digests of the
program's blocks: that is the matter of the coding of the queries. Which K a wire has. Nothing on
soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Flat.RecordSeed
import OnBytes.K.SeedBytes
import OnBytes.TypedOracleCompiler.Slice.EntryConv

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left
open OnBytes.Slice (recSeedK recSeedB seedOf seedBS seedBS_b blockBytes recZ)
open TypedOracleCompiler.Slice (seedOfC seedOfC_eq)
open _root_.Iop (Dig)

/-- The first b of K digests as an array of byte strings, written in two ways. -/
theorem ofFn_eq_range {b n K : ℕ} (hbn : b = n) (h : b ≤ K) (a : Fin K → Dig 256) :
    (Array.ofFn fun i : Fin b => Run.digToBytes (a (Fin.castLE h i))) =
      (Array.range n).map fun t =>
        if h' : t < K then Run.digToBytes (a ⟨t, h'⟩) else ByteArray.empty := by
  subst hbn
  refine Array.ext (by simp) fun i h1 _ => ?_
  have hi : i < b := by simpa using h1
  simp only [Array.getElem_ofFn, Array.getElem_map, Array.getElem_range]
  rw [dif_pos (lt_of_lt_of_le hi h)]
  rfl

/-- **The wire's seed is the program's own drawing**, on the bytes of the first digests. -/
theorem wire_recSeedK (T : Fmt.M1.Code) (lg s K : ℕ) (h : (seedBS lg s).b ≤ K)
    (a : Fin K → Dig 256) :
    recSeedK T lg s K h a = seedOfC lg s (seedsOfDigs .two lg s a) := by
  rw [seedOfC_eq]
  unfold recSeedK recSeedB seedsOfDigs seedsOf blockBytes
  rw [ofFn_eq_range (seedBS_b lg s) h a]
  rfl

/-- What the wire asks of K is what the tie asks. -/
theorem room_recSeedK {lg s K : ℕ} (h : (seedBS lg s).b ≤ K) : nBlocks lg s ≤ K := by
  unfold nBlocks
  rw [← seedBS_b]
  exact h

end OnBytes.K.Left
