-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GateFine.lean: the walk of Johnson/Meaning/GateData.lean in finer pieces: 64
distances a piece in the place of 1024. A definition alone.

Why. By measurement the memory of such an evaluation in Lean's kernel grows with the number of
steps: a piece of 1024 distances takes above 4 GB of the process's own memory, one of 64 below
0.8 GB.
  pieceOK k: the walk over the 64 distances from 64 k on (k = 256: the one distance 16384).
-/
import Johnson.Meaning.GateData

set_option autoImplicit false

namespace Meaning.Gate

open OnBytes.Model.Layer (fxOne)

/-- The walk over the distances from 64 k on: 64 of them, or the one distance 16384 at k = 256. -/
def pieceOK (k : ℕ) : Bool :=
  gateOK (stepOf 8) (if k == 256 then 1 else 64) (64 * k) (xAtS (stepOf 8) (64 * k) fxOne)

end Meaning.Gate
