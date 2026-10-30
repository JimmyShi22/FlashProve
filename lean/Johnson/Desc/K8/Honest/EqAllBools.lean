-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqAllBools.lean: THE SMALLNESS TEST (K8): THE PREMISE OF ITS RUN OF CLAIMS ON
SHAPES (EqPre, Johnson/Desc/K8/Honest/EqAllRun.lean) AS A Bool OF THE STATE. Definitions with their
laws; nothing is evaluated.

Why. EqPre is three tests on values at the state's own parts. Two are Bools already. The third,
LiveCols (Johnson/Desc/K8/Honest/EqAllReturns.lean: at the drawn element no column of a matrix on
which a read lies has the weight 0), is written with "for all". Whoever wants the premises of all
runs of a batching as one test with code wants each as a Bool with one lemma.

  **liveColsB_iff**   liveColsB (LiveCols with code: Johnson/Desc/K8/Honest/EqAllToy.lean, which has
                  the one direction liveCols_of_B) is true just where LiveCols holds.
  eqPreB s        EqPre, with code; true where the state's part is not there, as EqPre is.
  **eqPreB_iff**  it is true just where EqPre holds.
  eqPre_of_B      the one direction, as a lemma of its own.

Limits. liveColsB folds every column of every matrix on which a read lies: dear at the protocol's
sizes. It is a test on a drawn value: who shows that it accepts at a state of a run is not said.
liveColsB lies in a file of an example (EqAllToy.lean), which comes in beneath this file's one
import. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K8.Honest.EqAllRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (partOf)
open OnBytes.Tie.Pv.Tail.Port (readsList)

theorem liveColsB_iff (tl : HTailF2) (funs : Array HFun) (chi : E) :
    liveColsB tl funs chi = true ↔ LiveCols tl funs chi := by
  unfold liveColsB LiveCols
  rw [List.all_eq_true]
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  rw [List.all_eq_true]
  refine ⟨fun h c hc => ?_, fun h c hc => ?_⟩
  · have := h c (List.mem_range.2 hc)
    simpa using this
  · have := h c (List.mem_range.1 hc)
    simpa using this

/-- **The run's premises on the state, with code.** TRUE WHERE THE STATE HAS NO PART (partOf s =
none), as EqPre is. -/
def eqPreB (s : S) : Bool :=
  (partOf s).all fun q =>
    q.tl.funsHeld q.funs && (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE &&
      liveColsB q.tl q.funs q.F.theta

theorem eqPreB_iff (s : S) : eqPreB s = true ↔ EqPre s := by
  unfold eqPreB EqPre
  cases partOf s with
  | none => exact ⟨fun _ q h => (nomatch h), fun _ => rfl⟩
  | some q =>
    constructor
    · intro h q' hq'
      obtain rfl : q = q' := Option.some.inj hq'
      have h' : (q.tl.funsHeld q.funs && (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE &&
        liveColsB q.tl q.funs q.F.theta) = true := h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h'
      exact ⟨h'.1.1, h'.1.2, (liveColsB_iff _ _ _).1 h'.2⟩
    · intro h
      obtain ⟨h1, h2, h3⟩ := h q rfl
      show (q.tl.funsHeld q.funs && (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE &&
        liveColsB q.tl q.funs q.F.theta) = true
      rw [h1, h2, (liveColsB_iff _ _ _).2 h3]
      rfl

theorem eqPre_of_B {s : S} (h : eqPreB s = true) : EqPre s := (eqPreB_iff s).1 h

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.liveColsB_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPreB_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPre_of_B
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPreB
