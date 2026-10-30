-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastTaken.lean: the trees that the key file's last chain takes over, at the written place: just tree 0 and tree 5 of the
first chain and tree 1 of the shared chain. A closed line; and the premise `hmem` of `taken_trees` from two counts.

  `taken_PF`: the line.
  `hmem_key`: the premise.

What stays open. `c₁`, `c₂`: the first chain sends more than five trees, the shared chain more than one: counts of the two
chains in front of their last borders.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyThreadBase
import E2E.KeyShapeThirdFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource ownTest)
open AtPublicFiles.KeyThread (takenIn decl₃)
open AtPublicFiles.AtFiles.Full (PF)

/-- **The taken trees at the written place.** -/
theorem taken_PF : (takenIn (ownTest PF).rounds).all
    (fun σ => σ == .taken 0 0 || σ == .taken 0 5 || σ == .taken 1 1) = true := by decide +kernel

section
variable {Bk : ProverCoinCounts} {S₁ S₂ S₃ Cl V₁ W₁ X₁ P₁ V₂ W₂ X₂ P₂ V₃ W₃ X₃ P₃ : Type}
  (T₁ : Thread Bk S₁ Cl V₁ W₁ X₁ P₁) (T₂ : Thread Bk S₂ Cl V₂ W₂ X₂ P₂) (T₃ : Thread Bk S₃ Cl V₃ W₃ X₃ P₃)

/-- **Each tree taken over is at hand at its sender's last border.** -/
theorem hmem_key {n₁ n₂ : Nat} (ht : T₃.taken = takenIn (ownTest PF).rounds)
    (c₁ : 5 < treesTo T₁.bs n₁) (c₂ : 1 < treesTo T₂.bs n₂) :
    ∀ σ ∈ T₃.taken, (∃ j, σ = .taken 0 j ∧ Fmt.TreeSource.own j ∈ T₁.hand n₁) ∨
      (∃ j, σ = .taken 1 j ∧ Fmt.TreeSource.own j ∈ T₂.hand n₂) := by
  intro σ hσ
  rw [ht] at hσ
  have h := List.all_eq_true.1 taken_PF σ hσ
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  have m₁ : ∀ j, j < treesTo T₁.bs n₁ → Fmt.TreeSource.own j ∈ T₁.hand n₁ := fun j hj => by
    unfold Thread.hand
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  have m₂ : ∀ j, j < treesTo T₂.bs n₂ → Fmt.TreeSource.own j ∈ T₂.hand n₂ := fun j hj => by
    unfold Thread.hand
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  rcases h with (rfl | rfl) | rfl
  · exact Or.inl ⟨0, rfl, m₁ 0 (by omega)⟩
  · exact Or.inl ⟨5, rfl, m₁ 5 c₁⟩
  · exact Or.inr ⟨1, rfl, m₂ 1 c₂⟩

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.taken_PF
#print axioms AtPublicFiles.KeyLastChain.hmem_key
