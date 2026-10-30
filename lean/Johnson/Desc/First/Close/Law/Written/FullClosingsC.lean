-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/Written/FullClosingsC.lean: an evaluation in the kernel, cut off so
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
theorem full_part6 : closingsC (dryProofRunsFull0p6.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) =
      [(3295, some 7), (1324, some 8), (3295, some 7)] ∧
    lastZero (dryProofRunsFull0p6.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem full_part7 : closingsC (dryProofRunsFull0p7.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) =
      [(1324, some 8), (3295, some 7), (1324, some 8)] ∧
    lastZero (dryProofRunsFull0p7.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem full_part8 : closingsC (dryProofRunsFull0p8.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) =
      [(3295, some 7), (1322, some 8), (659, some 1)] ∧
    lastZero (dryProofRunsFull0p8.flatMap fun x =>
    (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))) = true := by
  decide +kernel

end VerifiableInference.Desc.First.Close
