-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/CloseHint.lean: THE CLOSING's STEP ON SHAPES (`closeGF`,
Johnson/Desc/K10/Honest/AtPair.lean) ONCE MORE, WITH A HINT FOR THE ONE LIST THAT IT SORTS:
`closeGFH`: A PAIR: A FUNCTION OF A HINT, THE STEP's NUMBERS AND A SHAPE, AND THE PROOF THAT closeGF
IS EQUAL TO IT AT EVERY HINT. THE SECOND TEXT IS WRITTEN NOWHERE: LEAN MAKES IT. No premise. One
definition.

Purpose. Beneath closeGF, `FormSh.fixLow` (Johnson/Desc/First/Shape/Makes.lean) calls mergeIdx,
which sorts. MergeIdxH.lean says what that costs Lean's kernel and how a hint spares it. Whoever
evaluates the closing's step may evaluate closeGFH.1 runs Q x in closeGF Q x's place, at the runs of
the list that the step leaves.

How. `⟨_, fun runs Q x => by delta closeGF closeGSM FormSh.fixLow; simp -zeta only [mergeIdx_H
runs]; delta mergeIdxH mergeIdx; simp -zeta only [mergeSort_eq]; rfl⟩`: delta lays the named
definitions' own texts open; simp rewrites by the named law; the closing rfl fills the hole with the
term that then stands there. The second delta and simp take the core's sort out of the fallback too.

Limits. WHAT A READER LOSES: THE SECOND TEXT CAN BE READ NOWHERE IN THIS FILE; `#print
ProofFile.Honest.K10.YesFree.closeGFH` shows it. THE TYPE IS MET BY THE IDLE FUNCTION (fun _ Q x =>
closeGF Q x, with rfl): nothing that is stated says that the hint is read or that a sort is spared.
ONE HINT FOR EVERY CALL OF mergeIdx BENEATH THE STEP: where it fits a call's list, that call's sort
is spared; at every other call the fallback sorts. That no List.mergeSort is left beneath the made
function is not stated and cannot be: it is seen by a walk over the made term's constants, outside
the library. The file stands under Johnson/AtFull/Shape/ and lays its one name into
ProofFile.Honest.K10.YesFree, the namespace of the step that it rewrites. Nothing is evaluated here; what
the made text costs is not said. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K10.Honest.AtPair
import Johnson.Unfolds.MergeSort
import Johnson.AtFull.Shape.MergeIdxH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First.Shape
open Johnson.AtFull.Shape.MergeIdxH (mergeIdxH mergeIdx_H)

/-- closeGF with mergeIdx beneath it rewritten by mergeIdx_H at the hint runs, and the sort in the
fallback by mergeSort_eq. The first field is made by Lean: the closing rfl fills it. The second
field is the tie: at every hint. -/
def closeGFH : { f : List (Nat × Nat) → Par → ChainF → Option ChainF //
    ∀ runs Q x, closeGF Q x = f runs Q x } :=
  ⟨_, fun runs Q x => by
    delta closeGF closeGSM FormSh.fixLow
    simp -zeta only [mergeIdx_H runs]
    delta mergeIdxH mergeIdx
    simp -zeta only [Johnson.Unfolds.mergeSort_eq]
    rfl⟩

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.closeGFH
