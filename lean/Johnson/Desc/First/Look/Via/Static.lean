-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/Via/Static.lean: the kind "lookup" (K3): the tests of the strict reading of
a round that read the plan's entry alone. One definition.

Why. The strict reading of a round (`roundT`, Johnson/Desc/First/Tape/Tape.lean) tests a view's
round and the plan's entry for it together. `staticT e` holds those of its tests, at the rule {},
that read the entry and no view: e.poss and e.trits are 0 (no position and no matrix entry is
drawn); e.rows is 0 and the name is not that of the round that batches rows; the kind of the name is
the kind asked; e.roots and e.answers are 0 and e.count is 1.
It stands in a file of its own, which imports no proof, so that the test that runs (`fitsVia`,
Johnson/Desc/First/Look/Via/Via.lean) and the premise that theorems on the hearing take are one
definition, and so that it can be evaluated on a plan's entries by itself.

Limits. Nothing here says that these are all of `roundT`'s tests that read the entry alone, or that
they are the right tests of an entry.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Tape.Tape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open VerifiableInference.Desc.First.Tape (kindAsked)

/-- **The tests of the strict reading of a round that read the entry alone.** -/
def staticT (e : Fmt.Entry) : Bool :=
  e.poss == 0 && e.trits == 0 && (e.rows == 0 && e.name != Model.RoundName.batSigma.name) &&
    Params.kindOf e.name == some (kindAsked e.name) &&
      (e.roots == 0 && e.answers == 0 && e.count == 1)

end VerifiableInference.Desc.K3
