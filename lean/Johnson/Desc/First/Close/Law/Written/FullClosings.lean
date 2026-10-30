-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Written/FullClosings.lean: the closings of the full size's written
list, out of its nine parts' (FullClosingsA, B, C): see RoundsWritten.lean's head.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Written.FullClosingsA
import Johnson.Desc.First.Close.Law.Written.FullClosingsB
import Johnson.Desc.First.Close.Law.Written.FullClosingsC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes.Params (Rounds)
open Johnson.G (dryProofFull dryProofSmall)
open Johnson.G

/-- The codes along some runs. -/
def codesAlong (runs : List (Nat × Nat)) : List (Nat × Nat) :=
  runs.flatMap fun x => (((dryProofRecsFull.map codeOf)[x.2]?).elim [] (List.replicate x.1))

theorem codesAlong_append (a b : List (Nat × Nat)) :
    codesAlong (a ++ b) = codesAlong a ++ codesAlong b := List.flatMap_append

/-- One part more behind parts whose closings are known. -/
theorem closings_step {a b : List (Nat × Nat)} {x y : List (Nat × Option Nat)}
    (ha : closingsC (codesAlong a) = x ∧ lastZero (codesAlong a) = true)
    (hb : closingsC (codesAlong b) = y ∧ lastZero (codesAlong b) = true) :
    closingsC (codesAlong (a ++ b)) = x ++ y ∧ lastZero (codesAlong (a ++ b)) = true := by
  rw [codesAlong_append]
  exact ⟨by rw [closingsC_append _ _ ha.2, ha.1, hb.1], lastZero_append _ _ hb.2⟩

/-- The 26 closings of the first chain's written list at the full size: the 25 links' and the last
group's. -/
theorem full_closings : closingsOf dryProofFull.1 =
    [(6, some 8), (3295, some 7), (1324, some 8), (3295, some 7), (1324, some 8), (3295, some 7),
      (1324, some 8), (3295, some 7), (1324, some 8), (3295, some 7), (1324, some 8),
      (3295, some 7), (1324, some 8), (3295, some 7), (1324, some 8), (3295, some 7),
      (1324, some 8), (3295, some 7), (1324, some 8), (3295, some 7), (1324, some 8),
      (3295, some 7), (1324, some 8), (3295, some 7), (1322, some 8), (659, some 1)] := by
  rw [closingsOf_eq]
  show closingsC ((unrunR dryProofRecsFull dryProofRunsFull0).map codeOf) = _
  rw [map_unrunR]
  exact (closings_step (closings_step (closings_step (closings_step (closings_step (closings_step
    (closings_step (closings_step full_part0 full_part1) full_part2) full_part3) full_part4)
    full_part5) full_part6) full_part7) full_part8).1

end VerifiableInference.Desc.First.Close
