-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/Kept/Full34.lean: an evaluation in the kernel, cut off so that no file
is heavy: `CornersAll`, or `CornersIf` at some first flags, at written lists of the full size
without repeats.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Kept.Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G

set_option maxRecDepth 1000000 in
theorem cornersFull_3 : CornersAll (linksFullLit.dedup.getD 3 []) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem cornersFull_4 : CornersAll (linksFullLit.dedup.getD 4 []) := by
  decide +kernel

end VerifiableInference.Desc.First.Close
