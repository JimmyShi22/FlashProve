-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Fact3.lean: A CLOSED FACT AT THE WRITTEN DATA (Full/Data.lean),
DECIDED BY LEAN's KERNEL, alone in its file: nothing is lacking.
Limits. At written data: that this is the makers' data at the public files is not said here. Nothing
on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Ask

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem c3_full :
    (lackingSk (placesSk spotsW ksW) ((framesSk shapeW ksW).map (·.1)) (onRoadSk batchAtW ksW)
      (eachAtSk spotsW ksW) (testsAtSk spotsW ksW) sharedW secondW).isEmpty = true := by
  decide +kernel

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.c3_full
