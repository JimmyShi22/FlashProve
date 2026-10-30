-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/FlatList.lean: the written shared chain's flat list (Johnson/Desc/K14/Blocks.lean:
chainOf), written out: a front block, the eight blocks of the linear claim's shared rounds (or the
one that fails its test on the plan), the proximity tests' blocks, the chain's end. Theorems.

  stAt · bare          the statement at the chain's record; a block as the flat list holds it: its
                       test on the plan is strengthened, nothing else of it is turned.
  steps_bare           so it steps as the block does.
  flat_tests · flat_mem   the list; what a member of it is.
What is not claimed. Nothing on what any block tests. Nothing on soundness.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.StepKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain VerifiableInference.Desc VerifiableInference.Desc.Keeps

/-- The statement at the shared chain's record. -/
abbrev stAt : St → Statement := fun d => d.st

/-- A block as the chain's flat list holds it. -/
abbrev bare (b : Block St Unit) : Block St Unit := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- The flat list's form of a block steps as the block does. -/
theorem steps_bare {R : St → St → Prop} {b : Block St Unit} (h : Steps R b) : Steps R (bare b) := by
  intro hp ft s rs cols s' k hs
  have hp' : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := hp
  exact h (Bool.and_eq_true _ _ ▸ hp').1 ft s rs cols s' k hs

/-- The shared chain's flat list, written out. -/
theorem flat_tests (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) :
    (chainOf c P tests last).blocksInOrder =
      ((bare (frontBlock c) :: (blocksOr P).map bare) ++ tests.map bare) ++
        [bare (last (blocksOr P ++ tests))] := by
  simp [chainOf, Chain.blocksInOrder, List.map_append]

/-- What a block of the flat list is. -/
theorem flat_mem (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) (b : Block St Unit)
    (hb : b ∈ (chainOf c P tests last).blocksInOrder) :
    (∃ b' ∈ frontBlock c :: blocksOr P, b = bare b') ∨ (∃ b' ∈ tests, b = bare b') ∨
      b = bare (last (blocksOr P ++ tests)) := by
  rw [flat_tests] at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
        exact Or.inl ⟨b', List.mem_cons_of_mem _ hb', rfl⟩
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      exact Or.inr (Or.inl ⟨b', hb', rfl⟩)
  · exact Or.inr (Or.inr (List.mem_singleton.1 hb))

end Desc.K14
