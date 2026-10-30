-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/FramesOk.lean: A CLOSED FACT AT THE WRITTEN DATA
(Full/Data.lean), DECIDED BY LEAN's KERNEL, alone in its file: none of the written lots' frames that
`framesSk` (SkelParts.lean) takes has a round.
Limits. At written data. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Ask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem frames_full : ((framesSk shapeW ksW).all fun x => x.2.nRounds == 0) = true := by
  decide +kernel

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.frames_full
