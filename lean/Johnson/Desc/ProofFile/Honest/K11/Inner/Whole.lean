-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Inner/Whole.lean: `HeadMergeInner`
(Honest/K11/Inner/Statement.lean) AS A THEOREM: `headMergeInner_of` (Honest/K11/Inner/Passes.lean)
with its four premises paid by the four theorems of the law of the masked sumcheck's honest part for
all callers: `sumHeard`, `sumClaim`, `sumLeft` (Honest/SumLaw/Law.lean), `sumLast`
(Honest/SumLaw/LawEnds.lean). The statement's own premises stand. One theorem.

What it says, in words: at true claims on units of a layout that are in order, at a ledger that is
ready, with the coins of the first run under the sumcheck's own slots: on the rounds of the honest
part played alone behind a batching round, the kind's own maker of the tape and its hearing return;
the form that its run of claims then makes is worth 0 in the world of the ledger behind and the mask
entries; and under the weights that are made for the rows the matrix, read at the merge's point,
plus beta times the coin is the end value as it was shown.

Limits. Those of the statement: the part stands unlifted and is played alone; nothing on the block's
decision on a state, on how the claims are made, or on which entries of which messages the coins
are. It rests on the files of Honest/SumLaw/. Values at which all of the
statement's premises hold together are typed in Member.lean of this folder. NOT COMPLETENESS of
anything: a lemma. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Inner.Passes
import Johnson.Desc.ProofFile.Honest.SumLaw.LawEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

theorem headMergeInner : HeadMergeInner :=
  headMergeInner_of SumLaw.sumHeard SumLaw.sumClaim SumLaw.sumLeft SumLaw.sumLast

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.headMergeInner
