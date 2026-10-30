-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RootsCount.lean: the plain data of a file count the third chain's roots as they were
read, though the data's third list of rounds is made at made-up names.

Statements and proofs. OnBytes/Maker/ReadSpecs.lean (`readChain_roots`) counts the roots of a chain
as read by the rounds from which its description was made. Two lists of rounds with the same items
have as many roots.

Main names:
  `rootsIn_of_items`: two lists of rounds with the same items have as many roots.
  `third_roots`: a chain read under a description made from the rounds R' has as many roots as a
    list R with the items of R'.
Limits: that the two lists have the same items is a premise (for the third chain:
OnBytes/Maker/RoundsAtTags.lean). Nothing on soundness.


-/
import OnBytes.Maker.ReadSpecs

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Three (rootsIn)
open OnBytes.Params (Rounds)

/-- Two lists of rounds with the same items have as many roots. -/
theorem rootsIn_of_items {R R' : Rounds} (h : R'.map (·.1.items) = R.map (·.1.items)) :
    rootsIn R' = rootsIn R := by
  have e := congrArg (fun l : List (List Fmt.Item) =>
    (l.map fun it => it.countP (· == .root)).sum) h
  simp only [List.map_map] at e
  exact e

/-- **The data count the chain's roots as read.** -/
theorem third_roots {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R R' : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (hS : Params.describeWith g label st rand R' ft = some S) (seen : Fmt.Seen) (b : ByteArray)
    (i : ℕ) (c : ChainRead) (e : readChain S seen b i = some (c.out, c.next))
    (h : R'.map (·.1.items) = R.map (·.1.items)) : rootsIn R = c.roots.length := by
  rw [← rootsIn_of_items h]
  exact (readChain_roots hS seen b i c e).symm

end OnBytes.Maker
