-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Fact2.lean: A CLOSED FACT AT THE WRITTEN DATA (Full/Data.lean),
DECIDED BY LEAN's KERNEL, alone in its file: the lots' blocks have no fault.
Limits. At written data: that this is the makers' data at the public files is not said here. Nothing
on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Ask

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem c2_full :
    (faultsSk spotsW shapeW batchAtW ksW).isEmpty = true := by
  decide +kernel

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.c2_full
