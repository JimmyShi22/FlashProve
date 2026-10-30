-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HonestCells.lean: THE TWO PREMISES ON THE CELLS OF "OPENED AT THE TRUTH" (Law/OpenedAll.lean) CAN BE MET TOGETHER: there are cells with
(dataOf c).Holds and HonestHead c.toCells. FOR A TOY MEMBER OF K06_law.
WHAT IT IS NOT, FIRST. THE HEAD's HALF IS MET EMPTILY: honestHead_uncosted is at a request AT WHICH NO POSITION HAS A COST (the one
checked position is the last: r = T - 1, e = T): there the policy's four forms (mean, count, clip, table) ask nothing
of the cells: HonestHead holds of ANY cells. So a member built on it shows nothing on costs, clips, the table of
exponentials or the policy. That honest cells meet HonestHead at a request WITH costs is shown by nothing here. The
norm's half is the honest cells of THE STREAM OF ZEROS (Law/NormHonest.lean: cellRelN_met). Nothing on the lookup's side
(the keys' ranges and rows). Nothing on soundness.
  (holds_of_rows, Law/NormJoint.lean: the clause rows of CellRelN gives the bridge's Holds: taken by name.)
  honestHead_uncosted  no position with a cost, RC = 0: HonestHead c, whatever c is.
  uncosted_last        at r = T - 1, e = T no position has a cost and RC = 0.
  honest_cells         under the tests on the plan, at such a request: there is c with Holds and HonestHead.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OpenedHead
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Kinds.Law.NormHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-- **Where no position has a cost the head's own half asks nothing of the cells.** -/
theorem honestHead_uncosted (c : Cells) (hc : ∀ t, t < T → costed t = false) (hR : RC = 0) :
    HonestHead c := by
  have z : ∀ (p : Pt) (Z : Nat → K), ((Finset.range T).sum fun t =>
      (if costed t = true then rd (eq p.zt t) else 0) * Z t) = 0 := fun p Z =>
    Finset.sum_eq_zero fun t ht => by
      rw [hc t (Finset.mem_range.mp ht)]
      simp
  refine ⟨fun t _ => ⟨?_, ?_⟩, ?_, ?_⟩
  · apply zero_of_rd (okE_clipAt c _)
    rw [rd_clipAt]
    exact z _ _
  · apply zero_of_rd (okE_tableAt c _)
    rw [rd_tableAt]
    exact z _ _
  · apply zero_of_rd (show okE (meanAt c) = true from okE_addMul _ _ _)
    rw [rd_mean, hR]
    have : ((Finset.range T).sum fun t => if costed t = true then
        numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t else 0) = 0 :=
      Finset.sum_eq_zero fun t ht => by rw [hc t (Finset.mem_range.mp ht)]; simp
    rw [this]
    simp
  · apply zero_of_rd (show okE (countAt c) = true from okE_addMul _ _ _)
    rw [rd_count, hR]
    have : ((Finset.range T).sum fun t => if costed t = true then
        numZ c .over t + numZ c .slackCap t else 0) = 0 :=
      Finset.sum_eq_zero fun t ht => by rw [hc t (Finset.mem_range.mp ht)]; simp
    rw [this]
    simp

/-- The last position alone is checked: no position has a cost. -/
theorem uncosted_last (hr : r = T - 1) (he : e = T) :
    (∀ t, t < T → costed t = false) ∧ RC = 0 := by
  refine ⟨fun t ht => ?_, ?_⟩
  · unfold costed checked
    rw [hr, he]
    by_cases h1 : t + 1 < T
    · have : ¬ (T - 1 ≤ t) := by omega
      simp [this]
    · simp [h1]
  · unfold RC
    rw [hr, he]
    omega

/-- **There are cells that meet both premises**, at a request whose one checked position is the last. -/
theorem honest_cells {sT : Nat} (hplan : planOk sT = true) (hr : r = T - 1) (he : e = T) :
    ∃ c : NCells, (dataOf c).Holds ∧ HonestHead c.toCells := by
  obtain ⟨c, hc⟩ := cellRelN_met hplan
  obtain ⟨h1, h2⟩ := uncosted_last hr he
  exact ⟨c, holds_of_rows c hc.rows, honestHead_uncosted c.toCells h1 h2⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.honest_cells
