-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/VecEnum.lean: a numbering of the vectors that a protocol sends, round by round.

 * `EncData.Enum s d`: for each round a numbering (Mathlib's `FinEnum`) of the vectors sent in it.
 * `EncData.Enum.ofNone`: that numbering for a protocol that sends no vector.
Notation: `EncData F E s`: for each round of s, how its oracle part is sent as vectors
(Blocks/BlockFront.lean); `EncData.All Q`: every vector of every round has the property Q of its
code, number of rows, number of row variables, role and number of positions read
(Blocks/StageSide.lean).
-/
import Blocks.StageSide
import Blocks.AlignedPlaces
import Blocks.Numbering

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/-- A numbering of the vectors of each round. -/
def EncData.Enum : (s : Shape) → EncData F E s → Type
  | [], _ => PUnit
  | _ :: s, (e, d) => FinEnum e.A × EncData.Enum s d

namespace EncData.Enum

/-- a protocol that sends no vector -/
def ofNone :
    (s : Shape) → (d : EncData F E s) → EncData.All (fun _ _ _ _ _ => False) s d → EncData.Enum s d
  | [], _, _ => PUnit.unit
  | _ :: s, (_, d), h =>
    (⟨0, ⟨fun a => (h.1 a).elim, fun i => i.elim0, fun a => (h.1 a).elim, fun i => i.elim0⟩⟩,
      ofNone s d h.2)

end EncData.Enum

end Blocks
