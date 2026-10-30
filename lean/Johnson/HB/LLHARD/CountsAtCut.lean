-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/CountsAtCut.lean: the two premises of Johnson/HB/LLHARD/ToldCounts.lean,
`CountsAre` and `TreesAre`, hold at what the written cut of the IOP as written in Lean tells
(`cutFirstFull`, Johnson/Desc/Ok/PlanWritten/CutLit.lean). So two written values that were made
apart agree: the cut, printed off the sub-protocols themselves, and the walk that hands the written
sendings to the written places.

Row or tool. Closed facts on written values. With them the facts of ToldCounts.lean stand at a
closed term for told, with no premise. No law on a sub-protocol is named.

The argument, its closed term and its tie.
  told: `cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)`: of each of the 358 rows the trees
    that its rounds tell. The term stands spelled out: others are typing a name for it and the
    tie from the test that compares the cut at a run.

    (Where this and lean/THEOREM.md differ, the page holds.)
    That tie is not named here: so no form in
    scope is stated.

What is here.
  `countsAre_cut`: at all 359 borders the written cut tells as many oracle messages and trees as the
    written sendings lay in front. `treesAre_cut`: tree by tree, as many tenants as the written
    layout has.
  `countsAre_cut_rejects`, `treesAre_cut_rejects`: the negative tests: with what the first teller
    tells struck out, neither holds.
  `planBelow_cut`: so `planBelowB LFull 358` accepts at that term. `planBelow_cut_rejects`: with the
    seats' trees moved behind the last tree it rejects.
  `cut_tells`: 358 rows, of which 78 tell; 83 trees: the term is not empty.
By evaluations in Lean's kernel (`decide +kernel`): all but `planBelow_cut`.

Limits. By the head of CutLit.lean no theorem says that its rows are those of the IOP as written in
Lean: a test compares them at a run. Nothing on soundness.


-/
import Johnson.HB.LLHARD.ToldCounts
import Johnson.Desc.Ok.PlanWritten.CutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutFirstFull)

set_option maxRecDepth 1000000 in
/-- **At all 359 borders the written cut tells what the written sendings lay.** -/
theorem countsAre_cut : CountsAre (cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)) := by
  unfold CountsAre
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Tree by tree, as many tenants.** -/
theorem treesAre_cut : TreesAre (cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)) := by
  unfold TreesAre
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with what the first teller tells struck out. -/
theorem countsAre_cut_rejects :
    ¬ CountsAre ((cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)).set 2 []) := by
  unfold CountsAre
  decide +kernel

set_option maxRecDepth 1000000 in
theorem treesAre_cut_rejects :
    ¬ TreesAre ((cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)).set 2 []) := by
  unfold TreesAre
  decide +kernel

/-- **The test accepts at the written cut.** -/
theorem planBelow_cut :
    planBelowB LFull 358 (cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)) = true :=
  planBelow_written countsAre_cut

set_option maxRecDepth 1000000 in
/-- The negative test: with the seats' trees moved behind the last tree. -/
theorem planBelow_cut_rejects :
    planBelowB { LFull with places := LFull.places.map fun x => (x.1 + LFull.shapes.length, x.2) }
      358 (cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- 358 rows, of which 78 tell; 83 trees. -/
theorem cut_tells :
    cutFirstFull.length = 358 ∧
      ((cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)).filter fun os => !os.isEmpty).length =
        78 ∧
      (cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)).flatten.length = 83 := by
  decide +kernel

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.countsAre_cut
#print axioms VerifiableInference.Desc.K13.Law.treesAre_cut
#print axioms VerifiableInference.Desc.K13.Law.countsAre_cut_rejects
#print axioms VerifiableInference.Desc.K13.Law.treesAre_cut_rejects
#print axioms VerifiableInference.Desc.K13.Law.planBelow_cut
#print axioms VerifiableInference.Desc.K13.Law.planBelow_cut_rejects
#print axioms VerifiableInference.Desc.K13.Law.cut_tells
