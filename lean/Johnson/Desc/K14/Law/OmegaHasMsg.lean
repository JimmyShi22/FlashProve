-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/OmegaHasMsg.lean: THE SHARED CHAIN's SENDING OF Omega HAS A MESSAGE, AT EVERY
SHAPE: by the make of linMessageOmega (OnBytes/Iop/Lin.lean: one notice, or two where the shape
splits). Three theorems.

  withOmega_pos      0 < (withOmega S).size.
  parO_sent          the sending's parameters bear just these notices.
  omegaShapes_pos    0 < (shapesOf (parO Q)).length.
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K1 (shapesOf)

theorem withOmega_pos (S : LinShape) : 0 < (withOmega S).size := by
  unfold withOmega linMessageOmega
  dsimp only
  split <;> simp

theorem parO_sent (Q : P14) : (parO Q).sent = withOmega Q.S := by
  simp [parO, parK1, VerifiableInference.Desc.K1.Par.sent]

theorem omegaShapes_pos (Q : P14) : 0 < (shapesOf (parO Q)).length := by
  unfold shapesOf
  rw [parO_sent]
  simpa using withOmega_pos Q.S

end Desc.K14.Law
