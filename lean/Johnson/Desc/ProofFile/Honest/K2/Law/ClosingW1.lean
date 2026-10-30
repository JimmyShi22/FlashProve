-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingW1.lean: the kind "the code switch" (K2): THE LIGHT
CLOSING TEST SAYS YES AT FIVE OF THE 25 PLACES OF THE CLOSED LIST: the places number 1, 6, 11, 16, 21. One of
five files of one form. Each theorem joins the stretches that Lean's kernel has checked in the files
of the folder CW/, one stretch of at most 5 segments a file, side by side.

By: closingAt_of_links, chunkReach_step (Honest/K2/Law/ClosingChunk.lean) · the files CW/.

Limits. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. A public test at zeros:
nothing on what a closing leaves, nothing on a run. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P01C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P06C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P06C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P11C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P11C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P11C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P16C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P16C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P16C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P16C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P21C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P21C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P21C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P21C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P21C20

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_1 : closingAt 1 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_zero 1) 2 chunkW_1_0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_6 : closingAt 6 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_zero 6) 5 chunkW_6_0) 2 chunkW_6_5)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_11 : closingAt 11 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 11) 5 chunkW_11_0) 5 chunkW_11_5) 2 chunkW_11_10)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_16 : closingAt 16 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 16) 5 chunkW_16_0) 5 chunkW_16_5) 5 chunkW_16_10) 2 chunkW_16_15)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_21 : closingAt 21 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 21) 5 chunkW_21_0) 5 chunkW_21_5) 5 chunkW_21_10) 5 chunkW_21_15) 2 chunkW_21_20)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingW_1
#print axioms ProofFile.Honest.K2.Law.closingW_6
#print axioms ProofFile.Honest.K2.Law.closingW_11
#print axioms ProofFile.Honest.K2.Law.closingW_16
#print axioms ProofFile.Honest.K2.Law.closingW_21
