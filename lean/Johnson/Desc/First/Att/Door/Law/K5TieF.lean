-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TieF.lean: kind K5 (an attention segment's own rounds): THE KIND's CLOSED TEST tie (K5TieWitness.lean: tieWW g) IN A FORM THAT LEAN's KERNEL CAN WALK.

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Why. tieWW stands over all three chains' written seats with the roots in front of a sending summed over all written rounds: there an evaluation in the kernel does not end. Another file holds the same seats made for the kernel (Johnson/P5T/PlanSeatsFull.lean: seatsAllFull).

Main names:
  `tieF g`: tieWW's own text, with seatsAllFull for the written seats.
  `tieWW_eq`: under E₂ : pseatsAllW = seatsAllFull the two are one.
Is it empty here? Sentences without a premise, and equations.
Limits. They speak of the written values.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5TieWitness
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc.First.Look (idxAt sigListCalls)

def tieF (g : ℕ) : Bool :=
  linkRestBy (viewW (2 * g + 1)) sentW (sigListCalls sentW (fun _ => 0) (2 * g + 1)) (P5T.numOfPlan P5T.seatsAllFull)
    (idxAt sentW (P5T.numOfPlan P5T.seatsAllFull) (2 * g + 1)) (2 * g + 1)

theorem tieWW_eq (E₂ : pseatsAllW = P5T.seatsAllFull) (g : ℕ) : tieWW g = tieF g := by
  unfold tieWW tieW tieF
  rw [E₂]

end H2K5.Door

#print axioms H2K5.Door.tieWW_eq
