-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsLater.lean: the proof of `HeadMergeKeepsLater`
(Johnson/Desc/K11/Returns/KeepsLaterStatement.lean), to the letter. A lemma; none of the library's
goals.

How. The clause writes the ledger behind out of the ledger in front: the next free number grows; the
number of slots stands; one entry of each of the three arrays is written, at the end value's slot,
which by the clause is not filled in front: an entry that is not written stands
(`getD_set_other`, OnBytes/Tie/Pv/Psc/PscFork.lean).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsLaterStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (zeroE)
open OnBytes.PscRun (Filled Sized getD_set_other)

/-- **The ledger only grows.** -/
theorem headMergeKeepsLater : HeadMergeKeepsLater := by
  intro P s s' hk
  obtain ⟨⟨a, wo, v, β, ha, _, _, _, hnf, _, e⟩, _⟩ := hk
  have hkeep : ∀ j, Filled a.F j →
      (a.F.gotF.set! (mergeEndSlot P.lay.lk a.F) true).getD j false = true ∧
      (a.F.vp.set! (mergeEndSlot P.lay.lk a.F) v).getD j zeroE = a.F.vp.getD j zeroE ∧
      (a.F.mf.set! (mergeEndSlot P.lay.lk a.F) β).getD j zeroE = a.F.mf.getD j zeroE := by
    intro j hj
    have hne : j ≠ mergeEndSlot P.lay.lk a.F := by
      rintro rfl
      exact hnf hj
    refine ⟨?_, getD_set_other _ _ _ _ _ hne, getD_set_other _ _ _ _ _ hne⟩
    rw [getD_set_other _ _ _ _ _ hne]
    exact hj
  have hnext : a.F.next ≤ a.F.next + 2 * P.lay.lk + 3 := by omega
  rw [e]
  refine ⟨a, _, ha, rfl, ⟨hnext, rfl, hkeep⟩, ⟨hnext, rfl, fun hs => ?_, hkeep⟩⟩
  exact ⟨by simpa using hs.1, by simpa using hs.2.1, by simpa using hs.2.2⟩

end Johnson.Desc.First.ForkMerge.Returns

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeKeepsLater
