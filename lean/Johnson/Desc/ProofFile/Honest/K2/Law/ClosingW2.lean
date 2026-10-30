-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingW2.lean: the kind "the code switch" (K2): THE LIGHT
CLOSING TEST SAYS YES AT FIVE OF THE 25 PLACES OF THE CLOSED LIST: the places number 2, 7, 12, 17, 22. One of
five files of one form. Each theorem joins the stretches that Lean's kernel has checked in the files
of the folder CW/, one stretch of at most 5 segments a file, side by side.

By: closingAt_of_links, chunkReach_step (Honest/K2/Law/ClosingChunk.lean) · the files CW/.

Limits. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. A public test at zeros:
nothing on what a closing leaves, nothing on a run. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P02C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P07C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P07C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P12C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P12C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P12C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P17C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P17C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P17C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P17C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P22C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P22C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P22C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P22C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P22C20

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_2 : closingAt 2 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_zero 2) 3 chunkW_2_0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_7 : closingAt 7 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_zero 7) 5 chunkW_7_0) 3 chunkW_7_5)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_12 : closingAt 12 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 12) 5 chunkW_12_0) 5 chunkW_12_5) 3 chunkW_12_10)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_17 : closingAt 17 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 17) 5 chunkW_17_0) 5 chunkW_17_5) 5 chunkW_17_10) 3 chunkW_17_15)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_22 : closingAt 22 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 22) 5 chunkW_22_0) 5 chunkW_22_5) 5 chunkW_22_10) 5 chunkW_22_15) 3 chunkW_22_20)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingW_2
#print axioms ProofFile.Honest.K2.Law.closingW_7
#print axioms ProofFile.Honest.K2.Law.closingW_12
#print axioms ProofFile.Honest.K2.Law.closingW_17
#print axioms ProofFile.Honest.K2.Law.closingW_22
