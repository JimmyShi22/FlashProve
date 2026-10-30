-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsOnce.lean: the proofs of the two statements of
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsOnceStatement.lean, to the letter. Lemmas; none of the
library's goals. Each is one call of `entryRunIs_once` (Honest/Small/EntryOnce.lean) at the kind's
address and the locks' letters; the second at i := 0.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsOnceStatement
import Johnson.Desc.ProofFile.Honest.Small.EntryOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

/-- **At the first lot's entry.** -/
theorem maskLotOnce : MaskLotOnce := by
  intro Xi F B pl P o sf base ν₀ hW hE a' hne e' he' ho' i hi
  exact entryRunIs_once hW hE a' hne e' he' ho' i hi

/-- **At the second lot's entry.** -/
theorem indexLotOnce : IndexLotOnce := by
  intro Xi F B pl o sf el hW hE a' hne e' he' ho'
  exact entryRunIs_once hW hE a' hne e' he' ho' 0 Nat.zero_lt_one

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.maskLotOnce
#print axioms ProofFile.Honest.K11.indexLotOnce
