-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CW/P12C10.lean: one stretch of the light closing test, by Lean's
kernel: at the place number 12, the segments 10 to 13. A closed fact; nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingChunk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunkW_12_10 : chunkOk 12 10 3 = true := by decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.chunkW_12_10
