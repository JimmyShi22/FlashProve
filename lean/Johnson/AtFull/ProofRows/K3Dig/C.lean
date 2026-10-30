-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Dig/C.lean: THE ENTRY TESTS' ROW ON THE LOOKUPS' DIGITS, DECIDED BY
LEAN's KERNEL AT THE WRITTEN VALUES (Johnson/AtFull/ProofRows/K3Full.lean), AT THE SEGMENTS 10 TO
14: one theorem a segment. One of five files, so that Lake builds them side by side: at each
segment the test calls the planner for the lookup's rounds and walks 2 ^ 11 joint rows.
Limits. Closed facts at written values. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000000

namespace Johnson.AtFull.ProofRows.K3
open VerifiableInference.Desc.K3Asks

theorem dig_10 : digOne setFull (pFull 10) (tFull 10) sentFull = true := by decide +kernel

theorem dig_11 : digOne setFull (pFull 11) (tFull 11) sentFull = true := by decide +kernel

theorem dig_12 : digOne setFull (pFull 12) (tFull 12) sentFull = true := by decide +kernel

theorem dig_13 : digOne setFull (pFull 13) (tFull 13) sentFull = true := by decide +kernel

theorem dig_14 : digOne setFull (pFull 14) (tFull 14) sentFull = true := by decide +kernel

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.dig_10
#print axioms Johnson.AtFull.ProofRows.K3.dig_11
#print axioms Johnson.AtFull.ProofRows.K3.dig_12
#print axioms Johnson.AtFull.ProofRows.K3.dig_13
#print axioms Johnson.AtFull.ProofRows.K3.dig_14
