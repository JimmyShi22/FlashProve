-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3SpecKnownProofs.lean: a lemma on the clauses on the stored trees. No Mathlib.


`storedOk_congr`: the clauses on the stored trees look at the statement only through "item number
k holds a root of 32 bytes".





Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M3SpecKnown
import Fmt.M3ParOfLawsProofs
import Fmt.M1SpecKnownProofs

namespace Fmt
namespace M3
open Fmt.M1 Fmt.M2

/-- `storedOk` looks at the statement through "the item number k holds a root of 32 bytes" alone. -/
theorem storedOk_congr (st st' : ByteArray)
    (h : ∀ k,
      ((itemRoot st k).any fun x => x.size == 32) = ((itemRoot st' k).any fun x => x.size == 32))
    (r : Round) (ts : List Stored) :
    storedOk st r ts = storedOk st' r ts := by
  unfold storedOk
  simp only [h]

end M3
end Fmt
