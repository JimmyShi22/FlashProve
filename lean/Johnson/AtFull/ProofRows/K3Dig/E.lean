-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Dig/E.lean: THE ENTRY TESTS' ROW ON THE LOOKUPS' DIGITS, DECIDED BY
LEAN's KERNEL AT THE WRITTEN VALUES (Johnson/AtFull/ProofRows/K3Full.lean), AT THE SEGMENTS 20 TO
24: one theorem a segment. One of five files, so that Lake builds them side by side: at each
segment the test calls the planner for the lookup's rounds and walks 2 ^ 11 joint rows.
Limits. Closed facts at written values. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000000

namespace Johnson.AtFull.ProofRows.K3
open VerifiableInference.Desc.K3Asks

theorem dig_20 : digOne setFull (pFull 20) (tFull 20) sentFull = true := by decide +kernel

theorem dig_21 : digOne setFull (pFull 21) (tFull 21) sentFull = true := by decide +kernel

theorem dig_22 : digOne setFull (pFull 22) (tFull 22) sentFull = true := by decide +kernel

theorem dig_23 : digOne setFull (pFull 23) (tFull 23) sentFull = true := by decide +kernel

theorem dig_24 : digOne setFull (pFull 24) (tFull 24) sentFull = true := by decide +kernel

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.dig_20
#print axioms Johnson.AtFull.ProofRows.K3.dig_21
#print axioms Johnson.AtFull.ProofRows.K3.dig_22
#print axioms Johnson.AtFull.ProofRows.K3.dig_23
#print axioms Johnson.AtFull.ProofRows.K3.dig_24
