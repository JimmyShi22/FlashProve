-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/WalkEnd.lean: Walk.catches, at a walk that ends at a statement which passes the
test for the end of a protocol.

LIMIT. FOUR OF THE THEOREM's PREMISES ARE NOT NEEDED: what it concludes follows from "Z is tidy"
alone, for all words (by reading, not by a theorem here): so without hEnd, hL, hM and hbad. It
locates nothing of a run: a walk ties its ends by tidiness alone (by reading, not by a theorem
here), so the statement, the group and the batching that it returns need be none that a run has
passed or a verifier has begun. See LIMIT in Johnson/Desc/Means/Walk.lean.

Johnson/Desc/Means/Walk.lean finds, on a walk from a statement of which Claims is false to one of
which it is true, a beginning of a test on some walk that takes the false claim in.
Johnson/Desc/Means/End.lean shows that a statement which passes the test for the end of a protocol
claims nothing any more. This file joins the two: no premise on the words at the end is left.

Main theorem: Walk.catches_to_end.

What is not claimed. That a chain is a walk. That the two invariants on notes and marks hold at the
end: they are conditions here. That the batching is one of the run: see LIMIT. No chance is named:
the count is for one batching, and a chain has several. Nothing on soundness.

-/
import Johnson.Desc.Means.Walk
import Johnson.Desc.Means.End

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] [IsDomain K] [Finite K] {ρ : Reading K}

/-- From a tidy statement to the end of a protocol: for all words of which not all holds that the
statement in front claims, some batching on some walk holds at few multipliers. Four of its premises
are not needed: see LIMIT in this file's head. -/
theorem Walk.catches_to_end {S Z : Statement} (h : Walk ρ S Z) (hT : Tidy S)
    (hEnd : (Z.groups.all (·.inRun) && Z.oracles.all fun x => !x.sampled || !x.groups.isEmpty) =
      true)
    (hL : ∀ (o : Nat) (x : Oracle) (g : Nat), Z.oracles[o]? = some x → g ∈ x.groups →
      ∃ G, Z.groups[g]? = some G ∧ o ∈ G.members)
    (hM : ∀ (i : Nat) (G : Group), Z.groups[i]? = some G → G.inRun = true → G.rows = #[])
    {m : Words K} (hbad : ¬ Claims ρ S m) :
    ∃ (J : Statement) (g : Nat) (G : Group), Walk ρ S J ∧ J.groups[g]? = some G ∧
      Walk ρ (Slice.begun J g G) Z ∧
      Nat.card {y : K // ∃ (x : E) (out : GroupRow) (T : Tables K), ρ.val x = y ∧
        Bat.combine (Slice.begun J g G) g ⟨layoutOf J G, Slice.runRows J G⟩ x = some out ∧
        LaidOn (Slice.begun J g G) (layoutOf J G) m T ∧
        GroupSays ρ (Slice.begun J g G) (layoutOf J G) out T} ≤ (Slice.runRows J G).size - 1 :=
  h.catches hT hbad (claims_end_of ρ hEnd hL hM (h.tidy hT).noneYet m)

end OnBytes.Means
