-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/Drawn/Small34.lean: an evaluation in the kernel, cut off so that no
file is heavy: `LayoutAll`, or `LayoutIf` at some first flags, at written lists of the small size
without repeats.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Drawn.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G

set_option maxRecDepth 1000000 in
theorem layoutSmall_3 : LayoutAll (linksSmallLit.dedup.getD 3 []) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem layoutSmall_4 : LayoutAll (linksSmallLit.dedup.getD 4 []) := by
  decide +kernel

end VerifiableInference.Desc.First.Close
