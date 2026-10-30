-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Written/FullClosingsA.lean: an evaluation in the kernel, cut off so
that no file is heavy: see RoundsWritten.lean's head.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Written.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes.Params (Rounds)
open Johnson.G (dryProofFull dryProofSmall)
open Johnson.G

set_option maxRecDepth 1000000 in
theorem full_part0 : closingsC (dryProofRunsFull0p0.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) =
      [(6, some 8), (3295, some 7)] ∧
    lastZero (dryProofRunsFull0p0.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem full_part1 : closingsC (dryProofRunsFull0p1.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) =
      [(1324, some 8), (3295, some 7), (1324, some 8)] ∧
    lastZero (dryProofRunsFull0p1.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem full_part2 : closingsC (dryProofRunsFull0p2.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) =
      [(3295, some 7), (1324, some 8), (3295, some 7)] ∧
    lastZero (dryProofRunsFull0p2.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) = true := by
  decide +kernel

end VerifiableInference.Desc.First.Close
