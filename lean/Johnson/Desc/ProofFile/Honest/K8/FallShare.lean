-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FallShare.lean: THE SMALLNESS TEST: A STATED NUMBER for the share
of the lists of challenges at which one of its tests on values behind the batching
(Honest/K8/Share.lean) says no, in one segment. A DEFINITION, WITH CODE. NO THEOREM, NO BOUND:
nothing holds the number against the tests.

WHERE THE NUMBERS COME FROM: the format's own counts (docs/format/FORMAT.md, 13.9, "Sampled values
at which a verifier gives no acceptance" and "What these tests cost"), event by event:
  event 2   all entries of a column of the drawn matrix are 0: 1 of 2^tau for each column
  events 3, 8   a weight is 0 at the batching element: each weight under test is a polynomial in
            that element with at most `top` roots (that page: its degree is below n, so n - 1):
            at most weights * top values
  event 4   the batching element is 0: 1 value
  event 5   two row weights of a matrix are equal: `meet` values: that page gives the number
            itself, not an upper estimate
  event 6   a weight of the claim on the lookup's keys is 0: a chance, over several draws, of at
            most 2 vZ of p^3
  event 7   a weight on a bit of a multiplicity is 0: a chance, over several draws, of at most 47
            of p^3
Events 3, 4, 5, 8 count values of the one batching element, out of the p^3 elements of the extension
field.
NOT COUNTED: that page has no count for the case that all coefficients of a weight which the reads
put on a digit are 0.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8

/-- The stated share, for one segment. columns: of all matrices of the place's list. weights: the
weights under test. top: the most roots of one weight in the batching element. meet: the count of
event 5. vZ: the number of levels of the key side of the lookup on the digits. -/
def k8FallShare (columns tau weights top meet vZ : Nat) : Odds :=
  (⟨columns, 2 ^ tau⟩ : Odds).plus ⟨weights * top + 1 + meet + 2 * vZ + 47, Code.pGold ^ 3⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8FallShare
