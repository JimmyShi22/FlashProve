-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K5/NoRounds.lean: the head's example: A CONTROL of the twelve closed facts g0 … g11
(Johnson/AtFull/K5/G0.lean …): ONE CLOSED FACT BY LEAN's KERNEL, A TRUE STATEMENT AT A BENT VALUE:
at the attention's plan of group 0 as publicOfO lays it (`atOwn`), with the first of own's two
score entries dropped, the count of rounds is not 162.
Where a maker refuses, atOwn is false: so this fact also says that the makers return.

Limits. One bend.
Two limits are raised in this file (maxRecDepth 1000000; maxHeartbeats 4000000 at the theorem). It
is imported by nothing. Nothing on soundness.
-/
import Johnson.AtFull.K5.AtOwn

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First VerifiableInference.Desc.First.Att.P H2K5.Row

set_option maxHeartbeats 4000000 in
theorem no_rounds :
    atOwn 0 (fun a => !decide (nRounds { a.own with score := a.own.score.tail } = 162)) = true := by
  decide +kernel

end Johnson.AtFull.K5

#print axioms Johnson.AtFull.K5.no_rounds
