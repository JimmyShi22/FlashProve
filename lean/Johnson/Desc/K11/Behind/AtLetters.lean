-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Behind/AtLetters.lean: the proof of `PromiseBehindStepAt`
(Johnson/Desc/K11/Behind/AtLettersStatement.lean), to the letter. A lemma; none of the library's
goals.

How: `promiseBehindStep` (Reached.lean of this folder): the two statements are one by definition.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Behind.AtLettersStatement
import Johnson.Desc.K11.Behind.Reached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Behind

/-- **The four behind the member's yes, at the library's own names for the head's letters.** -/
theorem promiseBehindStepAt : PromiseBehindStepAt :=
  promiseBehindStep

end Johnson.Desc.First.ForkMerge.Behind

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Behind.promiseBehindStepAt
