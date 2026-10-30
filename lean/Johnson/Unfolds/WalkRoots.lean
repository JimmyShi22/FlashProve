-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/WalkRoots.lean: `rootsC es rs` (Johnson/Unfolds/TreesAt.lean: at every round a count
over all of rs) follows from ONE walk down the rounds' roots and a SORTED rs (`walkN`,
Johnson/Unfolds/WalkLaw.lean).

  **`rootsC_of_walk`**: general.

Limits. That rs is sorted and that the walk accepts are premises. No closed fact.
Nothing on soundness.

-/
import Johnson.Unfolds.TreesAt
import Johnson.Unfolds.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds

/-- **The test on roots, from one walk.** -/
theorem rootsC_of_walk {es : List Fmt.Entry} {rs : List Nat} (hs : rs.Pairwise (· ≤ ·))
    (hw : walkN (es.map (·.roots)) 0 rs = true) : rootsC es rs = true := by
  unfold rootsC
  rw [List.all_eq_true]
  intro e he
  have hm : (e.1.roots, e.2) ∈ (es.map (·.roots)).zipIdx 0 := by
    rw [List.zipIdx_map]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  have h := walkN_sound (es.map (·.roots)) 0 rs hs (fun _ _ => Nat.zero_le _) hw _ hm
  simpa using h

end Johnson.Unfolds

#print axioms Johnson.Unfolds.rootsC_of_walk
