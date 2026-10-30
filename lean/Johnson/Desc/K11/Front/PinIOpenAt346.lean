-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/PinIOpenAt346.lean: the proof of the statement of
Johnson/Desc/K11/Front/PinIOpenAt346Statement.lean, to the letter: an evaluation in Lean's kernel on
the written lists. A lemma; none of the library's goals.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Front.PinIOpenAt346Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Front

set_option maxRecDepth 1000000 in
/-- **The item pinI is open at 346.** -/
theorem pinI_open_at_346 : PinIOpenAt346 := by
  unfold PinIOpenAt346
  decide +kernel

end Johnson.Desc.First.ForkMerge.Front

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Front.pinI_open_at_346
