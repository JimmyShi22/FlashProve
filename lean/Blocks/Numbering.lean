-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Numbering.lean: the numberings of oracle positions for two lists of rounds in a row, as data.

The compiled scheme turns oracle positions into leaves of a tree. For that it needs a numbering of
the positions of each round (`Shape.NumPos`, Iop/Num.lean). `numPosApp` gives the numberings for two
lists of rounds in a row (`pointApp`, Blocks/Basic.lean) from those of the two lists. (Other words
of this library: lean/GLOSSARY.md.)
-/
import Iop.WireOf
import Blocks.LevelDef
import Mathlib.Data.FinEnum

namespace Blocks
open Iop

def numPosApp :
    {s t : Shape} → {a : s.IsPoint} → {b : t.IsPoint} →
    s.NumPos a → t.NumPos b → Shape.NumPos (s ++ t) (pointApp a b)
  | [], _, _, _, _, y => y
  | _ :: _, _, (_, _), _, (x, xs), y => (x, numPosApp xs y)

end Blocks
