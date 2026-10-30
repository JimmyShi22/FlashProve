-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/GenOptional.lean: one optional addition of ZKCP/Optional.lean, in the form of ZKCP/Gen.lean.

Not part of the definitions of ZKCP/Defs.lean, and not used by Gen.IsZKCPArg. ZKCP/Optional.lean
states it for the form of a scheme in ZKCP/Defs.lean (`Arg`; one oracle): `HasExtractionError`. Here
is the same definition, word for word, for an argument system over a family of oracles (with
batches: the committer does not know of them).

  `HasExtractionError`  The optional requirement of ZKCP/Optional.lean, i* = i for the honest
                        committer: for every index i, the extractor's first part, given the honest
                        ivk and the honest committer's own trace, returns i, except with probability
                        δ.

The other addition of ZKCP/Optional.lean is session-augmented binding; it has no form here.
-/
import ZKCP.Gen

open scoped ENNReal

namespace ZKCP.Gen

variable {S : Rom.OSpec} {I X W IVK ISK Pf : Type}

/-- Correctness of extraction: i* = i for the honest committer, except with probability δ. -/
def HasExtractionError (A : Arg S I X W IVK ISK Pf) (E : Extractor S I X W IVK Pf) (δ : ℝ≥0∞) :
    Prop :=
  ∀ i, Rom.Pr (A.C i).withTrace (fun _ => {o | E.Ei o.1.1 o.2 ≠ some i}) ≤ δ

end ZKCP.Gen
