-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the statements of Johnson/M1/Numbers.lean, proved.
/-
Johnson/M1/NumbersProved.lean: `count`, `laid`, `countIsTight` by evaluation in Lean's kernel at the
written values; `rows` by one call of `rowsExact`. No property of the protocol is claimed here.
-/
import Johnson.M1.Numbers
import Johnson.SendSim.At.RowsExact

set_option autoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

set_option maxRecDepth 1000000 in
theorem count : Spec.count := by
  unfold Spec.count
  decide +kernel

set_option maxRecDepth 1000000 in
theorem laid : Spec.laid := by
  unfold Spec.laid
  decide +kernel

set_option maxRecDepth 1000000 in
theorem countIsTight : Spec.countIsTight := by
  unfold Spec.countIsTight
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The positions drawn for each of the first chain's trees, and for the number behind the last. -/
theorem drawn : (List.range 84).map (drawnTab tabM) =
    [219, 55] ++ List.replicate 75 219 ++ [55, 55, 55, 46, 44, 55, 0] := by decide +kernel

theorem rows : Spec.rows := fun i hi first data data' ds asks hs hn hb => by
  unfold shownLaw
  exact rowsExact (parAt i) first (rideAt i) data data' ds asks
    (List.all_eq_true.1 count.2.2.2 i (List.mem_range.2 hi)) hs hn hb

theorem numbers : Spec.numbers := ⟨count, laid, countIsTight, rows⟩

end OnBytes.M1

#print axioms OnBytes.M1.numbers
