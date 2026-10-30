-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyPlanesDefs.lean: three definitions on a lookup's range table and its counts, over
the field.

The data of a key file's written protocol (OnBytes/Slice/KeyData.lean) names the factor of a bit in
a leaf of a range table's tree and the vector of the counts' row. This file has their definitions,
below that file. What is proved of them is in OnBytes/Slice/KeyPlanesVals.lean (the vector of the
count).

Main definitions: `countPairs`, `valFrom`, `lfR`.

Not claimed. Nothing is proved here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeaves

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open Prob Cb

/-- The pairs of the vector of the count: (1, 2 ^ 2 ^ t) for each plane variable t, and (1, 1) for
each row variable. -/
def countPairs (mu d : ℕ) : List (GE × GE) :=
  ((List.range mu).map fun t => ((1 : GE), (2 : GE) ^ 2 ^ t)) ++ List.replicate d (1, 1)

/-- The value of a list of coordinates, the highest first, behind the value r: each step doubles and
adds. -/
def valFrom : GE → List GE → GE
  | r, [] => r
  | r, x :: xs => valFrom (2 * r + x) xs

/-- The factor of a bit in a leaf, round by round: alpha - 1 - the range table's extension at
the first d coordinates, the highest first. -/
def lfR (d : ℕ) (a : GE) (q : List GE) : GE := a - 1 - valFrom 0 (q.take d)

end OnBytes.Slice.Planes
