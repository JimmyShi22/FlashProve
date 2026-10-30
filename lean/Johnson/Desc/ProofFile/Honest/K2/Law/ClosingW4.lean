-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingW4.lean: the kind "the code switch" (K2): THE LIGHT
CLOSING TEST SAYS YES AT FIVE OF THE 25 PLACES OF THE CLOSED LIST: the places number 4, 9, 14, 19, 24. One of
five files of one form. Each theorem joins the stretches that Lean's kernel has checked in the files
of the folder CW/, one stretch of at most 5 segments a file, side by side.

By: closingAt_of_links, chunkReach_step (Honest/K2/Law/ClosingChunk.lean) · the files CW/.

Limits. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. A public test at zeros:
nothing on what a closing leaves, nothing on a run. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P04C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P09C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P09C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P14C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P14C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P14C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P19C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P19C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P19C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P19C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P24C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P24C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P24C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P24C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P24C20

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_4 : closingAt 4 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_zero 4) 5 chunkW_4_0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_9 : closingAt 9 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_zero 9) 5 chunkW_9_0) 5 chunkW_9_5)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_14 : closingAt 14 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 14) 5 chunkW_14_0) 5 chunkW_14_5) 5 chunkW_14_10)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_19 : closingAt 19 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 19) 5 chunkW_19_0) 5 chunkW_19_5) 5 chunkW_19_10) 5 chunkW_19_15)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_24 : closingAt 24 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 24) 5 chunkW_24_0) 5 chunkW_24_5) 5 chunkW_24_10) 5 chunkW_24_15) 5 chunkW_24_20)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingW_4
#print axioms ProofFile.Honest.K2.Law.closingW_9
#print axioms ProofFile.Honest.K2.Law.closingW_14
#print axioms ProofFile.Honest.K2.Law.closingW_19
#print axioms ProofFile.Honest.K2.Law.closingW_24
