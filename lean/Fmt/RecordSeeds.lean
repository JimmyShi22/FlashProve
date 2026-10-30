-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/RecordSeeds.lean: definitions alone: the seeds of a stored table's record, drawn with the hash
as an argument.
A stored table's record has seeds: points with a factor each, at which the table's rows are answered
(R4.8). They are in no file. Whoever needs them draws them from the table's name: a chain of its own
(a chain is the non-interactive form of one protocol), under the label 2 ^ 32, with 32 zero bytes in
the place of the parameters' digest and the name as its statement; one round of the kind "seeds"
with an empty message and no work; then `a` seeds, each a point of `v` coordinates and a factor that
is not 0 (R6.9).
Defines: `recordSeedsW h f name v a`: the drawing, over a monad m and a hash h with values in m; it
returns nothing where the chain's step refuses. `recordSeeds`: that at the format's own hash.
`flatSeeds`: the seeds as one list of elements: seed by seed, the coordinates of the point, then the
factor.
States: no theorem (theorems on these: Fmt/RecordSeedsLaws.lean). Under: no hypothesis.
Does not show:
(1) The name is an argument and is related to nothing here: not to a shape, a digest or a root. So
    are `v` and `a`.
(2) The text is that of `Known56.recordSeeds`, which is written at the format's own hash, with
    `recordFirstW h` and `Chain.queryW h` in the places of `recordFirst` and `Chain.query`. That the
    two agree is tested (by a check outside this file), not proved.
(3) The programs' own drawing is related to this one by no theorem.

-/
import Fmt.Rules5
import Fmt.Rules6Round

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-- The seeds of a stored table's record (R4.8, R6.9): a seeds, each with a point of v coordinates,
from the table's name. The first value of the record's chain is one call of h; the round's answer is
fetched in as many blocks as a seeds can use at most (18 words for a coordinate, 36 for a factor).
Nothing where the chain's step refuses (`Chain.queryW`, Fmt/Rules5.lean). -/
def recordSeedsW {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (f : Fld) (name : ByteArray)
    (v a : Nat) : m (Option (List (List Ext × Ext))) := do
  let rho0 ← recordFirstW h name
  match ← (⟨recordLabel, rho0, 0⟩ : Chain).queryW h ByteArray.empty .seeds 0 0
      (blocksFor (a * (v * 18 + 36))) with
  | none => pure none
  | some (_, vb) => pure (some (((drawSeed f v).times a (rowOf vb) 0).1))

/-- `recordSeedsW` at the format's own hash. -/
def recordSeeds (f : Fld) (name : ByteArray) (v a : Nat) : Option (List (List Ext × Ext)) :=
  recordSeedsW (m := Id) formatHash f name v a

/-- The seeds as one list of elements: seed by seed, the coordinates of its point, then its factor
(the order of `drawSeedL`, Fmt/Rules6Round.lean). -/
def flatSeeds (l : List (List Ext × Ext)) : List Ext := l.flatMap fun y => y.1 ++ [y.2]

end Fmt
