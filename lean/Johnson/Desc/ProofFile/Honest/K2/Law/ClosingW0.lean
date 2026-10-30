-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingW0.lean: the kind "the code switch" (K2): THE LIGHT
CLOSING TEST SAYS YES AT FIVE OF THE 25 PLACES OF THE CLOSED LIST: the places number 0, 5, 10, 15, 20. One of
five files of one form. Each theorem joins the stretches that Lean's kernel has checked in the files
of the folder CW/, one stretch of at most 5 segments a file, side by side.

By: closingAt_of_links, chunkReach_step (Honest/K2/Law/ClosingChunk.lean) · the files CW/.

Limits. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. A public test at zeros:
nothing on what a closing leaves, nothing on a run. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P00C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P05C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P05C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P10C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P10C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P10C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P15C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P15C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P15C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P15C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P20C00
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P20C05
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P20C10
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P20C15
import Johnson.Desc.ProofFile.Honest.K2.Law.CW.P20C20

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_0 : closingAt 0 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_zero 0) 1 chunkW_0_0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_5 : closingAt 5 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_zero 5) 5 chunkW_5_0) 1 chunkW_5_5)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_10 : closingAt 10 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 10) 5 chunkW_10_0) 5 chunkW_10_5) 1 chunkW_10_10)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_15 : closingAt 15 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 15) 5 chunkW_15_0) 5 chunkW_15_5) 5 chunkW_15_10) 1 chunkW_15_15)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem closingW_20 : closingAt 20 = true :=
  closingAt_of_links (by decide +kernel)
    (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_step (chunkReach_zero 20) 5 chunkW_20_0) 5 chunkW_20_5) 5 chunkW_20_10) 5 chunkW_20_15) 1 chunkW_20_20)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingW_0
#print axioms ProofFile.Honest.K2.Law.closingW_5
#print axioms ProofFile.Honest.K2.Law.closingW_10
#print axioms ProofFile.Honest.K2.Law.closingW_15
#print axioms ProofFile.Honest.K2.Law.closingW_20
