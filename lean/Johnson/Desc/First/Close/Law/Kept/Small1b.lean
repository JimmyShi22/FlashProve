-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/Kept/Small1b.lean: an evaluation in the kernel, cut off so that no file
is heavy: `CornersAll`, or `CornersIf` at some first flags, at written lists of the small size
without repeats.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Kept.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G

set_option maxRecDepth 1000000 in
theorem cornersSmall_1_2 : CornersIf (linksSmallLit.dedup.getD 1 []) true false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem cornersSmall_1_3 : CornersIf (linksSmallLit.dedup.getD 1 []) true true := by
  decide +kernel

end VerifiableInference.Desc.First.Close
