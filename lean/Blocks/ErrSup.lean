-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ErrSup.lean: if every error of a list, as a probability, is at most c, it is at most every
c' ≥ c (`below_mono`).

Notation: `s`: a `Shape` (Iop/Shape.lean): the list of a protocol's rounds, in order; `ε`: an
`Err s` (Iop/Rbr.lean): one number for each round: how many values of the challenge may lead from a
doomed transcript to one that is not doomed; `Err.Below ε c` (Iop/InteractiveOracleProof.lean): every error of the
list, as a probability, is at most c.
These errors are the numbers of a list (`ε : Err s`: any list of counts, for any `s`): that a
protocol is sound at the numbers of a list is no statement of this file.
-/
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Blocks

open Iop
open scoped ENNReal

/-- If every error of a list, as a probability, is at most c, it is at most every c' ≥ c. -/
theorem below_mono :
    ∀ {s : Shape} {ε : Err s} {c c' : ℝ≥0∞}, c ≤ c' → Err.Below ε c → Err.Below ε c'
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), _, _, hc, h => ⟨h.1.trans (mul_le_mul_left hc _), below_mono hc h.2⟩

end Blocks
