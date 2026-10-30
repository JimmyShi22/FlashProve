-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/PlanPasses.lean: A FILE's DECISION SAYS YES ONLY WHERE EVERY BLOCK's OWN TEST ON THE
PLAN HAS PASSED. So a law that holds of a block's step "where its test on the plan passes"
(Johnson/Desc/StepKeeps.lean: Steps) can be spent behind a yes of the file's decision without a
premise on the plan. Theorems.

  runCore_word         the decision's course says yes only where no word of refusal on the plan is
                       there.
  planOk_of_runEnd     a yes of FileDescription.runEnd: the tests on the plan pass.
  blocksOk_mem         what "all of a chain's blocks pass" gives of one block.
  planOk_blocks        the tests on the plan give every block's own, chain by chain.
  runEnd_blocks        **the two together.**
What is not claimed. Nothing on what a block's test on the plan asks.

-/
import Johnson.Desc.ChainEndFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps

/-- The decision's course says yes only where no word of refusal on the plan is there. -/
theorem runCore_word {Cl S₁ S₂ S₃ : Type} (planWord : Option String) (okStart : Bool) (s₁ : S₁)
    (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : Nat) (b₁ : List (Block S₁ Cl))
    (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl)) (fin : S₁ → S₂ → S₃ → Bool)
    (v₁ v₂ v₃ : Fmt.View) (e : S₁ × S₂ × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e) :
    planWord = none := by
  cases planWord with
  | none => rfl
  | some w =>
    unfold runCore at h
    dsimp only at h
    obtain ⟨_, hx, _⟩ := ChainEnd.bind_ok h
    simp [throw, throwThe, MonadExceptOf.throw] at hx

variable {Xi : Type}

/-- A yes of the decision: the tests on the plan pass. -/
theorem planOk_of_runEnd (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (e : F.S₁ × F.S₂ × F.S₃) (h : F.runEnd x v₁ v₂ v₃ = .ok e) : F.planOk = true := by
  have hw := runCore_word _ _ _ _ _ _ _ _ _ _ _ _ _ e h
  unfold FileDescription.planWord at hw
  split at hw
  · assumption
  · cases hw

/-- What "all of a chain's blocks pass" gives of one block. -/
theorem blocksOk_mem {S Cl : Type} (bs : List (Block S Cl)) (h : blocksOk bs = true) :
    ∀ b ∈ bs, b.planOk = true := by
  intro b hb
  have := List.all_eq_true.1 h b hb
  rw [Bool.and_eq_true] at this
  exact this.1

/-- The tests on the plan give every block's own, chain by chain. -/
theorem planOk_blocks (F : FileDescription Xi) (h : F.planOk = true) :
    (∀ b ∈ F.first.blocksInOrder, b.planOk = true) ∧ (∀ b ∈ F.shared.blocksInOrder, b.planOk = true) ∧
      ∀ b ∈ F.second.blocksInOrder, b.planOk = true := by
  unfold FileDescription.planOk at h
  rw [Bool.and_eq_true] at h
  have hc := h.1
  unfold FileDescription.planOkCore at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, a⟩, b⟩, c⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨blocksOk_mem _ a, blocksOk_mem _ b, blocksOk_mem _ c⟩

/-- **Behind a yes of a file's decision every block's own test on the plan has passed.** -/
theorem runEnd_blocks (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (e : F.S₁ × F.S₂ × F.S₃) (h : F.runEnd x v₁ v₂ v₃ = .ok e) :
    (∀ b ∈ F.first.blocksInOrder, b.planOk = true) ∧ (∀ b ∈ F.shared.blocksInOrder, b.planOk = true) ∧
      ∀ b ∈ F.second.blocksInOrder, b.planOk = true :=
  planOk_blocks F (planOk_of_runEnd F x v₁ v₂ v₃ e h)

end VerifiableInference.Desc.Keeps
