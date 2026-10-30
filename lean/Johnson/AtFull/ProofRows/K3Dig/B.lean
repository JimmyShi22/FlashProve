-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Dig/B.lean: THE ENTRY TESTS' ROW ON THE LOOKUPS' DIGITS, DECIDED BY
LEAN's KERNEL AT THE WRITTEN VALUES (Johnson/AtFull/ProofRows/K3Full.lean), AT THE SEGMENTS 5 TO
9: one theorem a segment. One of five files, so that Lake builds them side by side: at each
segment the test calls the planner for the lookup's rounds and walks 2 ^ 11 joint rows.
Limits. Closed facts at written values. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000000

namespace Johnson.AtFull.ProofRows.K3
open VerifiableInference.Desc.K3Asks

theorem dig_5 : digOne setFull (pFull 5) (tFull 5) sentFull = true := by decide +kernel

theorem dig_6 : digOne setFull (pFull 6) (tFull 6) sentFull = true := by decide +kernel

theorem dig_7 : digOne setFull (pFull 7) (tFull 7) sentFull = true := by decide +kernel

theorem dig_8 : digOne setFull (pFull 8) (tFull 8) sentFull = true := by decide +kernel

theorem dig_9 : digOne setFull (pFull 9) (tFull 9) sentFull = true := by decide +kernel

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.dig_5
#print axioms Johnson.AtFull.ProofRows.K3.dig_6
#print axioms Johnson.AtFull.ProofRows.K3.dig_7
#print axioms Johnson.AtFull.ProofRows.K3.dig_8
#print axioms Johnson.AtFull.ProofRows.K3.dig_9
