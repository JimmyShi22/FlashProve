-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Fact4.lean: A CLOSED FACT AT THE WRITTEN DATA (Full/Data.lean),
DECIDED BY LEAN's KERNEL, alone in its file: the blocks at the places are `baseW`.
Limits. At written data: that this is the makers' data at the public files is not said here. Nothing
on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Ask

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem c4_full :
    okIs ((placesSk spotsW ksW).mapM fun x => x.2) baseW = true := by
  decide +kernel

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.c4_full
