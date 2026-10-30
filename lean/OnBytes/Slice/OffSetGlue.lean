-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OffSetGlue.lean: two facts on strings of the format's call number 169, which the join
at tables of the oracle's values wants.

OnBytes/Slice/JoinAtSet.lean (`join_id_at`) asks that no key's code is among the strings (`hid`; a
key is a `Tie.IdKey`: a shape, 32 bytes, a table; not the key file), and that its event does not get
lost when the entries at the strings are left out of both logs (`hoff₀`, `hoff₁`).
OnBytes/Slice/WalkOff.lean shows, for a part of the library's compiler, that what it reads off a log
does not see a string of the format's call number 169 (`IsCall169`). This file has the like for a
key's code and for the first key in a log; for a part whose reading is made of a look's walks it
stands in OnBytes/Slice/WalksO.lean (`PartO.ByWalks.raw_offSet`).

Main theorems.
 `idCode_ne_call169`   no key's code is a string of the call number 169: so `hid` holds where all
     strings are such.
 `firstId_offSet`      the first key that a log holds for a digest (`Tie.firstId`) is the same
     without the entries at such strings.

What is not claimed. That two looks agree does not give `PartO.ByWalks.raw_offSet`'s condition for
leaves: a look may read such a string as a leaf that the reading then drops; the walk then ends at
that string, and without it may end at another. No event of the join is shown to meet `hoff₀` or
`hoff₁`: none is written. Facts on lists and strings; no probability.

-/
import OnBytes.Slice.WalkOff
import OnBytes.Slice.ByWalks
import OnBytes.Tie.IdOff

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch
open OnBytes.Tie (IdKey idCode firstId)

/-- No key's code is a string of the call number 169. -/
theorem idCode_ne_call169 (k : IdKey) {s : List Bool} (hs : IsCall169 s) : idCode k ≠ some s := by
  obtain ⟨half, t, i, st, bs, -, -, rfl⟩ := hs
  exact Tie.idCode_ne_call (n := 169) (by decide) half t i st bs k

/-- The first key that a log holds for a digest is the same without the entries at strings of the
call number 169. -/
theorem firstId_offSet (S : Finset (List Bool)) (hS : ∀ s ∈ S, IsCall169 s)
    (d : ZKCP.Digest 256) (σ : Trace (rom 256)) : firstId d (offSet S σ) = firstId d σ :=
  Tie.firstId_filter d _ σ fun e _ he => by
    obtain ⟨half, t, i, st, bs, -, -, h⟩ := hS e.2.1 (by simpa using he)
    rw [h]
    exact Tie.idRead_call (by decide) half t i st bs

end OnBytes.Slice
