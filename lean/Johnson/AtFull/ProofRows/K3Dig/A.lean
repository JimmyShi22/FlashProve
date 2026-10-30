-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Dig/A.lean: THE ENTRY TESTS' ROW ON THE LOOKUPS' DIGITS, DECIDED BY
LEAN's KERNEL AT THE WRITTEN VALUES (Johnson/AtFull/ProofRows/K3Full.lean), AT THE SEGMENTS 0 TO
4: one theorem a segment. One of five files, so that Lake builds them side by side: at each
segment the test calls the planner for the lookup's rounds and walks 2 ^ 11 joint rows.
Limits. Closed facts at written values. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000000

namespace Johnson.AtFull.ProofRows.K3
open VerifiableInference.Desc.K3Asks

theorem dig_0 : digOne setFull (pFull 0) (tFull 0) sentFull = true := by decide +kernel

theorem dig_1 : digOne setFull (pFull 1) (tFull 1) sentFull = true := by decide +kernel

theorem dig_2 : digOne setFull (pFull 2) (tFull 2) sentFull = true := by decide +kernel

theorem dig_3 : digOne setFull (pFull 3) (tFull 3) sentFull = true := by decide +kernel

theorem dig_4 : digOne setFull (pFull 4) (tFull 4) sentFull = true := by decide +kernel

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.dig_0
#print axioms Johnson.AtFull.ProofRows.K3.dig_1
#print axioms Johnson.AtFull.ProofRows.K3.dig_2
#print axioms Johnson.AtFull.ProofRows.K3.dig_3
#print axioms Johnson.AtFull.ProofRows.K3.dig_4
