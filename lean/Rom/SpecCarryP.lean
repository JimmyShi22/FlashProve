-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecCarryP.lean: a commit-and-prove argument with another prover. A definition; generic in the
scheme.

  `withP A P'`  the scheme (A.C, P', A.V); used, among others, in Compile/Batch/StarKE.lean
                (`argBKE`)

This library does not state or prove that (C, P', V) has what (C, P, V) has if no one can tell P'
from P. One case is covered: if (P' k b).runEager g = (A.P k b).runEager g for all k, b, g, then
`Gen.Arg.SameRun.of` with `Gen.Arg.SameRunVia.isZKCPArgWith_iff` (ZKCP/GenSameRun.lean) gives
`IsZKCPArgWith` for both schemes or neither, with the same extractor, simulator and bounds; no
declaration states it for `withP`.

Notation:
  k, b, g: a key k : ISK, a batch b : List (X × W), and g : `Fam S`: a whole family of functions
      (Rom/OSpec.lean)
  `runEager g` (Rom/OComp.lean): the oracles fixed: the law of the output over the coins only
  `Gen.Slots Pf b` (ZKCP/Gen.lean): one entry for each slot of the batch b: a list of the same
      length
-/
import Rom.Carry
import Rom.Forget
import Rom.EagerLazy

open scoped ENNReal

namespace Rom

open ZKCP Prob

variable {S : OSpec} {I X W PP IVK IVK' ISK Pf Pf' : Type}

/-- the scheme with another prover -/
def withP (A : Gen.Arg S I X W IVK ISK Pf)
    (P' : ISK → (b : List (X × W)) → OComp S (Gen.Slots Pf b)) : Gen.Arg S I X W IVK ISK Pf :=
  ⟨A.C, P', A.V⟩

end Rom
