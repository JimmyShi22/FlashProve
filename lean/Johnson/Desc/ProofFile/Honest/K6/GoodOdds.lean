-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodOdds.lean: the count of Honest/K6/Good.lean's first test as a
share, in the form in which Honest/Frame.lean writes a stated share. One definition with code;
no theorem.

Limits. A NUMBER THAT IS WRITTEN DOWN. What it is meant for: the chance that, of the challenges of
the sub-protocol "the output head's own rounds", one of the elements that `goodK6` reads is 0, if
each is drawn uniformly from the extension field: at most so many of the field's number of elements.
Nothing here holds it against the test in a space of challenges, and nothing says how challenges are
drawn.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Good
import Johnson.Desc.ProofFile.Honest.Frame
import Code.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc.Kinds (Head.Par)

/-- **The stated number**: `goodK6Events` of the number of elements of the extension field, the
cubic extension of the integers modulo 2^64 - 2^32 + 1. A stated number, no bound. -/
def goodK6Odds (p : Head.Par) : Odds := ⟨goodK6Events p, Code.pGold ^ 3⟩

end ProofFile.Honest.K6
