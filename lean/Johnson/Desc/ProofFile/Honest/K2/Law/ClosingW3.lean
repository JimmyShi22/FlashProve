-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingW3.lean: the kind "the code switch" (K2): THE LIGHT
CLOSING TEST SAYS YES AT FIVE OF THE 25 PLACES OF THE CLOSED LIST: the places number 3, 8, 13, 18, 23. One of
five files of one form. Each theorem joins the stretches that Lean's kernel has checked in the files
of the folder CW/, one stretch of at most 5 segments a file, side by side.

By: closingAt_of_links, chunkReach_step (Honest/K2/Law/ClosingChunk.lean) · the files CW/.

Limits. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. A public test at zeros:
nothing on what a closing leaves, nothing on a run. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P03C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P08C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P08C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P13C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P13C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P13C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P18C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P18C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P18C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P18C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P23C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P23C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P23C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P23C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P23C20

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_3 : closingAt 3 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_zero 3) 4 chunkW_3_0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_8 : closingAt 8 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_zero 8) 5 chunkW_8_0) 4 chunkW_8_5)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_13 : closingAt 13 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 13) 5 chunkW_13_0) 5 chunkW_13_5) 4 chunkW_13_10)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_18 : closingAt 18 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 18) 5 chunkW_18_0) 5 chunkW_18_5) 5 chunkW_18_10) 4 chunkW_18_15)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_23 : closingAt 23 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 23) 5 chunkW_23_0) 5 chunkW_23_5) 5 chunkW_23_10) 5 chunkW_23_15) 4 chunkW_23_20)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingW_3
#print axioms ProofFile.Honest.K2.Law.closingW_8
#print axioms ProofFile.Honest.K2.Law.closingW_13
#print axioms ProofFile.Honest.K2.Law.closingW_18
#print axioms ProofFile.Honest.K2.Law.closingW_23
