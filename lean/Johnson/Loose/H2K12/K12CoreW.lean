-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12PlacesCore
import Johnson.Loose.H2K12.K12TreesOf
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.G.SendsWritten
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.SliceFoldl
import Johnson.Unfolds.MergeSort
/-
Johnson/Loose/H2K12/K12CoreW.lean: THE PROXIMITY TEST's (the kind K12's) ROW: THE ONE
EVALUATION: AT THE WRITTEN VALUES THE ROUTINE THAT MAKES THE KIND's FOUR MEMBERS OFF THE PLAN
RETURNS THE FOUR WRITTEN MEMBERS. Alone in its file, since it is an evaluation in Lean's kernel of
unmeasured cost.
  coreAtW          placesCore (H2K12/K12PlacesCore.lean) at: recordSet, proofSizedFull, proofThree's
                   three lists and their plans, proofSendsFull; the count 25; the cut ⟨0, 48237, …,
                   77, the written stages⟩ (H2K12/K12CutW.lean: locsP, cutW); and for the three
                   lists of trees: treesOf (H2K12/K12TreesOf.lean) at the written sendings, with no
                   entry that is no round (offP0, offP1, offP2)
  coreW            coreAtW returns, has a place for Omega's test, and H2U.proximityTestParametersAt lays its four places
                   as piLFull and as piUFull, piOFull, piWFull laid at ⟨2, none, 9⟩, ⟨2, none, 10⟩,
                   ⟨3, none, 2⟩ (fourAt, H2K12/K12MemberOfParts.lean)
HOW. The sendings' labels go through String.splitOn and String.toNat?, the trees through
List.mergeSort: routines of Lean's library that its kernel does not unfold (of the first two seen by
the writers' own trial: each asked both ways, neither reduced; of the third by the head of the
file that cures it). FOUR GENERAL LAWS, IN THREE FILES, CALLED, bring them to forms
that it does: Johnson.Unfolds.splitOn_eq, toNat?_eq, slice_toNat?_eq, mergeSort_eq
(Johnson/Unfolds/SplitOn.lean, SliceFoldl.lean, MergeSort.lean). The
recipe: rewrite by these, then decide.
WHAT IT IS NOT: the written values stand on prints of the library's own planner and evaluator: this
file ties them to each other, not to any public files. treesOf is what treesSent returns WHERE it
returns (trees_are): that it returns is not said here. The full size alone. No soundness statement.
Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan H2U Johnson.Unfolds
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.G (proofSendsFull)
open H2K.Member (piLFull piUFull piOFull piWFull)

/-- The routine's short part at the written values. -/
def coreAtW : Except String Places4 :=
  placesCore recordSet proofSizedFull [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]
    proofThree.A.plan.plan proofThree.B.plan.plan proofThree.C.plan.plan proofSendsFull 25
    ⟨0, 48237,
      ((proofThree.A.plan.rounds.map (·.entry)).drop 48237).take
        (1 + towerLen proofSizedFull.request.last),
      77, proofSizedFull.request.last⟩
    (treesOf "proof file, first chain" proofSendsFull.1 0 [])
    (treesOf "proof file, shared chain" proofSendsFull.2.1 0
      (ownMasks proofSendsFull.2.1.codes proofSizedFull.batch.shape
        proofThree.B.plan.plan.rounds))
    (treesOf "proof file, second chain" proofSendsFull.2.2 0 [])

/-- **AT THE WRITTEN VALUES: THE FOUR WRITTEN MEMBERS.** -/
theorem coreW :
    fourAt coreAtW piLFull ({ piUFull with place := ⟨2, none, 9, .K12⟩ } : P12)
      ({ piOFull with place := ⟨2, none, 10, .K12⟩ } : P12)
      ({ piWFull with place := ⟨3, none, 2, .K12⟩ } : P12) = true := by
  simp only [coreAtW, treesOf, sentAt, sendTag, splitOn_eq, toNat?_eq, slice_toNat?_eq,
    mergeSort_eq]
  decide +kernel

end H2K12

#print axioms H2K12.coreW
