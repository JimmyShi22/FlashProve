-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/FirstAtFrame.lean: the premise hFirst of ColsAtStageFirst.lean
(`colsOf_first`: each tree below the stretch's base is the first tree at hand with its key) at the
frame that the rule of composition has for a file's first chain: the trees at hand are `allOf D`,
the keys are `D.key₁`. Statements and proofs; no definition.

  `find_range`     in the list of the numbers below n, the first number whose key is j's is j, if
                   the key of every number up to j is that number
  `first_of_id`    THE STATEMENT: from "the key of a tree below t is its number" and t ≤ nAll D
  `first_at_stage` the same in the words of `colsOf_first`, at the stage ⟨a, base, allOf D, ds,
                   D.key₁, allOf D⟩ with base ≤ t
Limits. THE PREMISE hid (the key of every tree below t is its number) IS NOT SHOWN HERE AT ANY DATA.
It is meant at t := D.t₁, the number of trees that the first chain sends. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.ColsAtStageFirst
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes.Maker
open VerifiableInference.Desc.Sound (allOf nAll)

theorem find_range (key : Nat → Nat) (n j : Nat) (hj : j < n) (hid : ∀ i, i ≤ j → key i = i) :
    (List.range n).find? (fun i => key i == key j) = some j := by
  rw [List.find?_range_eq_some]
  refine ⟨by simp, List.mem_range.2 hj, ?_⟩
  intro i hi
  have h1 := hid i (Nat.le_of_lt hi)
  have h2 := hid j (Nat.le_refl j)
  simp only [h1, h2, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  omega

/-- **Each tree below t is the first of all the file's trees with its key.** -/
theorem first_of_id (D : WholeD) (t : Nat) (ht : t ≤ nAll D) (hid : ∀ j, j < t → D.key₁ j = j) :
    ∀ j, j < t → ((allOf D).find? fun L => D.key₁ L.no == D.key₁ j).map (·.no) = some j := by
  intro j hj
  unfold allOf
  rw [List.find?_map]
  have h := find_range D.key₁ (nAll D) j (Nat.lt_of_lt_of_le hj ht)
    (fun i hi => hid i (Nat.lt_of_le_of_lt hi hj))
  have e : ((fun L : LeftT => D.key₁ L.no == D.key₁ j) ∘
      fun j => (⟨j, (D.depth j).getD 0⟩ : LeftT)) = fun i => D.key₁ i == D.key₁ j := rfl
  rw [e, h]
  rfl

/-- The same in the words of `colsOf_first`. -/
theorem first_at_stage (D : WholeD) (a base : Nat) (ds : List RDT) (t : Nat) (hb : base ≤ t)
    (ht : t ≤ nAll D) (hid : ∀ j, j < t → D.key₁ j = j) :
    ∀ j, j < (⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).base →
      ((⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).Lin.find? fun L =>
        (⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).key L.no ==
          (⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).key j).map (·.no) = some j :=
  fun j hj => first_of_id D t ht hid j (Nat.lt_of_lt_of_le hj hb)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.find_range
#print axioms VerifiableInference.Desc.First.K2.first_of_id
#print axioms VerifiableInference.Desc.First.K2.first_at_stage
