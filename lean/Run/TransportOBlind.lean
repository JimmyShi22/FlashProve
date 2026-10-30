-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TransportOBlind.lean: the extractor that recomputes is blind: its witness part reads neither
the proof nor the prover's trace, also after it has been brought down to the one oracle and into
the audited syntax.

Statements and proofs: each by definition. "Brought down to the one oracle" means: translated from
typed oracles to the single oracle by a coding m (`extractorOverOneHashFunction m`). "Into the audited syntax" means:
into the types of ZKCP/Defs.lean (`Special.extOf`).

Why: Run/TransportO.lean carries binding over to a scheme whose verifier first parses a string with
the oracle's help, for a blind extractor (`Run.Blind`). This file shows that the hypothesis is met
by the extractor that recomputes.

Main names:
  The extractor that recomputes (CompileK/Recompute.lean: `Gen.recompute E tr w0`): the index as E
    extracts it from the key and the committer's trace; the witness := tr (that index) (the
    instance), a fixed value where no index is extracted.
  Brought down to the one oracle (Rom/ExitBind.lean: `extractorOverOneHashFunction m`) and into the audited syntax
    (ZKCP/SpecialDefs.lean: `Special.extOf`): both only translate the two traces and hand the proof
    on.
  `Spec.blind_recompute`: Blind (Special.extOf (extractorOverOneHashFunction m (Gen.recompute E tr w0))), for every
    coding m, every E, tr, w0.



Limits: this file does not say anything on an extractor that reads the proof. It does not say that
a blind extractor is worth much as a "knowledge" extractor: the extractor that recomputes finds the
index in the committer's trace, and the witness is a function of index and instance: what binding
then says of a proof is that its instance lies in the language of the extracted index, with that
witness.

Terms: lean/GLOSSARY.md.
-/
import Run.TransportO
import ZKCP.SpecialDefs
import Rom.ExitBind
import CompileK.WideLang
import CompileK.KnowWidePass
import CompileK.Recompute
import CompileK.KnowLocal

set_option autoImplicit false

namespace Run
open ZKCP Rom

namespace Spec

def blind_recompute : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (I X W IVK Pf : Type) (m : OracleCoding S lam)
      (E : Gen.Extractor S I X Unit IVK Pf) (tr : I → X → W) (w0 : W),
    Blind (Special.extOf (extractorOverOneHashFunction m (Gen.recompute E tr w0)))

end Spec

theorem blind_recompute : Spec.blind_recompute := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

end Run
