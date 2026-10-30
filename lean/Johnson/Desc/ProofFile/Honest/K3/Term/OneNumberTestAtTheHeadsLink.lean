-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ON WRITTEN VALUES ALONE: NO LETTER.
Johnson/Desc/ProofFile/Honest/K3/Term/OneNumberTestAtTheHeadsLink.lean: the honest side of the kind
"lookup" (K3): THE TEST "one" (`oneV`, Johnson/Desc/First/Att/Door/Law/K5OneView.lean) ACCEPTS AT THE
WRITTEN VALUES OF THE FULL SIZE AT THE HEAD's LINK, number 24: one decision of Lean's kernel.

Why. The library has that decision at the 24 links in front of the head's (`one_written`,
Johnson/Desc/First/Att/Door/Law/K5OneWritten.lean). The lookup on the head's calls reads committed
symbols too.

  `oneNumberTestAcceptsAtTheHeadsLinkAtWrittenValues`   `H2K5.Door.oneW 24 = true`

Limits. A closed fact on written values: that a public part has these values is another file's. The
test's last arm says yes where a place lies beyond the calls' list: whether an entry meets the
first arm at this link is not shown here (no negative test is laid). Nothing on any property.
-/
import Johnson.Desc.First.Att.Door.Law.K5OneWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written values, at link 24.** -/
theorem oneNumberTestAcceptsAtTheHeadsLinkAtWrittenValues : H2K5.Door.oneW 24 = true := by
  decide +kernel

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.oneNumberTestAcceptsAtTheHeadsLinkAtWrittenValues
