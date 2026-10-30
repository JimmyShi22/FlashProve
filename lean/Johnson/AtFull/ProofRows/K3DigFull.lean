-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3DigFull.lean: THE ENTRY TESTS' ROW ON THE LOOKUPS' DIGITS AT THE
WRITTEN VALUES (Johnson/AtFull/ProofRows/K3Full.lean), AT ALL 25 SEGMENTS: gathered from the five
files Johnson/AtFull/ProofRows/K3Dig/A.lean to E.lean, in which Lean's kernel decides it segment
by segment; with two negative tests by the kernel. Three theorems.
  `dig_full`: `digOne` (Johnson/AtFull/ProofRows/K3Views.lean) says yes at every i below 25.
    `dig_bend_mask`: at no mask code it says no at segment 0. `dig_bend_piece`: with the low
    digits' piece one column narrower it says no at segment 0.
Why segment by segment. One decision over the whole list of 25 did not go through Lean (after 210
s: "did not reduce"); at single segments it does, in some 17 s each.
Limits. Closed facts at written values. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3Dig.A
import Johnson.AtFull.ProofRows.K3Dig.B
import Johnson.AtFull.ProofRows.K3Dig.C
import Johnson.AtFull.ProofRows.K3Dig.D
import Johnson.AtFull.ProofRows.K3Dig.E

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K3Asks

/-- **THE DIGITS' ROW AT THE WRITTEN VALUES.** -/
theorem dig_full : ∀ i, i < 25 → digOne setFull (pFull i) (tFull i) sentFull = true
  | 0, _ => dig_0
  | 1, _ => dig_1
  | 2, _ => dig_2
  | 3, _ => dig_3
  | 4, _ => dig_4
  | 5, _ => dig_5
  | 6, _ => dig_6
  | 7, _ => dig_7
  | 8, _ => dig_8
  | 9, _ => dig_9
  | 10, _ => dig_10
  | 11, _ => dig_11
  | 12, _ => dig_12
  | 13, _ => dig_13
  | 14, _ => dig_14
  | 15, _ => dig_15
  | 16, _ => dig_16
  | 17, _ => dig_17
  | 18, _ => dig_18
  | 19, _ => dig_19
  | 20, _ => dig_20
  | 21, _ => dig_21
  | 22, _ => dig_22
  | 23, _ => dig_23
  | 24, _ => dig_24
  | n + 25, h => absurd h (by omega)

set_option maxRecDepth 10000000 in
/-- A negative test: at no mask code. -/
theorem dig_bend_mask :
    digOne setFull (pFull 0) (tFull 0)
      { sentFull with codes := { sentFull.codes with mask := #[] } } = false := by
  decide +kernel

set_option maxRecDepth 10000000 in
/-- A negative test: the low digits' piece one column narrower. -/
theorem dig_bend_piece :
    digOne setFull (pFull 0)
      { tFull 0 with z1 := { (tFull 0).z1 with
          pieces := (tFull 0).z1.pieces.map fun p => { p with Cp := p.Cp - 1 } } }
      sentFull = false := by
  decide +kernel

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.dig_full
#print axioms Johnson.AtFull.ProofRows.K3.dig_bend_mask
#print axioms Johnson.AtFull.ProofRows.K3.dig_bend_piece
