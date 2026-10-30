-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SplitEntryWritten.lean: ONE DEFINITION, IN A FILE OF ITS OWN SO
THAT WHOEVER NAMES IT NEED NOT STAND OVER THE FILES THAT SPEAK OF IT: splitEntryWritten: the one
entry of the frame's book (Ahead, Johnson/Desc/ProofFile/Honest/Frame.lean) by which, at the
library's written description, the shared chain's split spends one coin of the part at "send
o_omega". A written value; no statement.

Who says what of it. That it is the written short list's second entry, and what stands behind it:
behind_omega_named (Honest/K14/SharedAheadOwners.lean). That the frame's splitEntry yields it at the
written description and sendings: rawSplit_written (AtFullSide/K14/RawSmallWritten.lean).

Limits. Nothing is stated here. Nothing on soundness, on completeness or on what is hidden; no
property.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- The written list's second entry: the split's one coin. -/
def splitEntryWritten : Ahead :=
  ⟨"the split's mask message to 2.-.8.0: split",
    ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 1⟩, ⟨⟨2, none, 8, .K14⟩, 0⟩, true⟩

end ProofFile.Honest.K14
