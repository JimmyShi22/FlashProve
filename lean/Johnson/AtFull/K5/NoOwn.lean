-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K5/NoOwn.lean: the head's example: A CONTROL of the twelve closed facts g0 … g11
(Johnson/AtFull/K5/G0.lean …): ONE CLOSED FACT BY LEAN's KERNEL, A TRUE STATEMENT AT A BENT VALUE:
at the attention's plan of group 0 as publicOfO lays it (`atOwn`), with own's number of pairs set
to 0, the test planOkOwn rejects.
Where a maker refuses, atOwn is false: so this fact also says that the makers return.

Limits. One bend, AND ONE THAT THE TEST's OWN SECOND CLAUSE DECIDES AT EVERY RECORD: it shows that
the test can reject, no more. The test's third clause (each sum's shape) is bent nowhere.
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
theorem no_own : atOwn 0 (fun a => !planOkOwn { a.own with pairs := 0 }) = true := by
  decide +kernel

end Johnson.AtFull.K5

#print axioms Johnson.AtFull.K5.no_own
