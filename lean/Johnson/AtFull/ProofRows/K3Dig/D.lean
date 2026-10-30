-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Dig/D.lean: THE ENTRY TESTS' ROW ON THE LOOKUPS' DIGITS, DECIDED BY
LEAN's KERNEL AT THE WRITTEN VALUES (Johnson/AtFull/ProofRows/K3Full.lean), AT THE SEGMENTS 15 TO
19: one theorem a segment. One of five files, so that Lake builds them side by side: at each
segment the test calls the planner for the lookup's rounds and walks 2 ^ 11 joint rows.
Limits. Closed facts at written values. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000000

namespace Johnson.AtFull.ProofRows.K3
open VerifiableInference.Desc.K3Asks

theorem dig_15 : digOne setFull (pFull 15) (tFull 15) sentFull = true := by decide +kernel

theorem dig_16 : digOne setFull (pFull 16) (tFull 16) sentFull = true := by decide +kernel

theorem dig_17 : digOne setFull (pFull 17) (tFull 17) sentFull = true := by decide +kernel

theorem dig_18 : digOne setFull (pFull 18) (tFull 18) sentFull = true := by decide +kernel

theorem dig_19 : digOne setFull (pFull 19) (tFull 19) sentFull = true := by decide +kernel

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.dig_15
#print axioms Johnson.AtFull.ProofRows.K3.dig_16
#print axioms Johnson.AtFull.ProofRows.K3.dig_17
#print axioms Johnson.AtFull.ProofRows.K3.dig_18
#print axioms Johnson.AtFull.ProofRows.K3.dig_19
