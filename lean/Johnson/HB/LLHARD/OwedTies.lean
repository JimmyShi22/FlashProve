-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/OwedTies.lean: three equations by definition that three files of this folder left
owed.

Row or tool. Tools. Nothing is evaluated but by unfolding.

What is here.
  `moreSpelt_is`: `moreSpelt` (PlusMoreWritten.lean) is `Sound.moreAll`
    (Johnson/Desc/Sound/MoreAll.lean), the composed filling's closed list of extra public tests.
  `links_same`: the two lists of the 25 segments' sorts are one: `K13.Law.linksFull`
    (Johnson/Desc/K13/Law/AtTableRow.lean), at which the facts of PlusMoreWritten.lean stand, and
    `Sound.linksFull` (Johnson/Desc/Sound/AtDriver.lean), which the law's binders name. The head of
    PlusMoreWritten.lean names the second where the first is meant.
  `told_is`: the term for what the written cut tells, as CountsAtCut.lean and
    SentAtWritten.lean [not in this library]
    spell it out, is `First.toldCut` (Johnson/Desc/First/CutWritten.lean).
  `countsAre_at_toldCut`, `treesAre_at_toldCut`: so the two premises of ToldCounts.lean hold at
    `toldCut`.

Limits. Nothing on soundness.


-/
import Johnson.HB.LLHARD.PlusMoreWritten
import Johnson.HB.LLHARD.CountsAtCut
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.First.CutWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.PlanWritten (cutFirstFull)

theorem moreSpelt_is : moreSpelt = VerifiableInference.Desc.Sound.moreAll := rfl

theorem links_same :
    VerifiableInference.Desc.K13.Law.linksFull = VerifiableInference.Desc.Sound.linksFull := rfl

theorem told_is :
    (cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)) =
      VerifiableInference.Desc.First.toldCut := rfl

theorem countsAre_at_toldCut : CountsAre VerifiableInference.Desc.First.toldCut := countsAre_cut

theorem treesAre_at_toldCut : TreesAre VerifiableInference.Desc.First.toldCut := treesAre_cut

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.moreSpelt_is
#print axioms VerifiableInference.Desc.K13.Law.links_same
#print axioms VerifiableInference.Desc.K13.Law.told_is
#print axioms VerifiableInference.Desc.K13.Law.countsAre_at_toldCut
#print axioms VerifiableInference.Desc.K13.Law.treesAre_at_toldCut
