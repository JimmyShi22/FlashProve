-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/Numbering.lean: two definitions for numberings of positions, with slots.

What is numbered are the oracle positions of a round (`Shape.NumPos`, Iop/Num.lean: for each round a
numbering of its oracle positions: it fixes the leaf of the Merkle tree that holds a position). In a
round of a protocol with slots (`BatchInteractiveOracleProof`, Iop/Batch.lean) the positions of the shared component
and those of a slot's component are numbered separately (`Shape.NumPosB`). The numberings are data.
`numPosBApp`: the numbering of s ++ t from those of s and of t. `numPosBShared`: see its docstring.
Limits: no numberings for a given protocol or for the record of protocols `BatchProtocol` (Iop/Batch.lean).
-/
import Blocks.Numbering
import Iop.BatchWireOf
import Blocks.Batch.Hvzk
import Blocks.Batch.Sound
import Blocks.ErrSup
import Blocks.LevelAcc
import Blocks.LevelLocal
import Blocks.LevelSound
import Blocks.LinkHVZK_rs
import Blocks.LinkSound
import Blocks.Reads
import Iop.RbrLast
import Mathlib.Data.FinEnum

namespace Blocks
open Iop

/-! ## Helper definitions -/

def numPosBApp :
    {s t : Shape} → {A : RoundSplits s} → {B : RoundSplits t} → {a : s.IsPoint} → {b : t.IsPoint} →
    s.NumPosB A a → t.NumPosB B b → Shape.NumPosB (s ++ t) (RoundSplits.app A B) (pointApp a b)
  | [], _, _, _, _, _, _, y => y
  | _ :: _, _, (_, _), _, (_, _), _, (x0, xJ, xs), y => (x0, xJ, numPosBApp xs y)

/-- the numbering if in all rounds only the shared component is sent -/
def numPosBShared (k : Kind) :
    (s : Shape) → (pts : s.IsPoint) → s.NumPos pts → s.NumPosB (RoundSplits.const (RAnn.ofShared k) s) pts
  | [], _, _ => ()
  | r :: s, (pt, pts), (np, nps) =>
    ((RAnn.numOfShared k r pt np).1, (RAnn.numOfShared k r pt np).2, numPosBShared k s pts nps)

end Blocks
