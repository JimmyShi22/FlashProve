-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DescRunsProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/DescRuns.lean.

Limits: those of Johnson/Desc/Sound/DescRuns.lean.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.DescRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker (runRow)

/-- The decision's course gives three ends just where each of its tests says yes. -/
theorem runCore_ok {S₁ S₂ S₃ Cl : Type} (pw : Option String) (ok : Bool) (s₁ : S₁) (s₂ : S₂)
    (start₃ : S₁ → S₂ → Except String S₃) (ft : Nat) (b₁ : List (Block S₁ Cl))
    (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl)) (fin : S₁ → S₂ → S₃ → Bool)
    (v₁ v₂ v₃ : Fmt.View) (e₁ : S₁) (e₂ : S₂) (e₃ : S₃) :
    runCore pw ok s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ↔
      pw = none ∧ ok = true ∧ viewWordsBelowPrime v₁ = true ∧ viewWordsBelowPrime v₂ = true ∧ viewWordsBelowPrime v₃ = true ∧
        chainAt "the first chain" 0 b₁ s₁ (withEmptySealRound v₁) = .ok e₁ ∧
        chainAt "the shared chain" 0 b₂ s₂ v₂ = .ok e₂ ∧
        (∃ s₃, start₃ e₁ e₂ = .ok s₃ ∧ chainAt "the second chain" ft b₃ s₃ v₃ = .ok e₃) ∧
        fin e₁ e₂ e₃ = true := by
  unfold runCore
  cases pw with
  | some w =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.1
  | none =>
  cases ok with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2.1
  | true =>
  cases viewWordsBelowPrime v₁ with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2.2.1
  | true =>
  cases viewWordsBelowPrime v₂ with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2.2.2.1
  | true =>
  cases viewWordsBelowPrime v₃ with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2.2.2.2.1
  | true =>
  cases chainAt "the first chain" 0 b₁ s₁ (withEmptySealRound v₁) with
  | error m =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2.2.2.2.2.1
  | ok a₁ =>
  cases chainAt "the shared chain" 0 b₂ s₂ v₂ with
  | error m =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2.2.2.2.2.2.1
  | ok a₂ =>
  conv => lhs; lhs; whnf
  cases h₃ : start₃ a₁ a₂ with
  | error m =>
    refine ⟨fun h => ?_, ?_⟩
    · cases h
    · rintro ⟨-, -, -, -, -, ha, hb, ⟨t, ht, -⟩, -⟩
      cases ha
      cases hb
      rw [h₃] at ht
      cases ht
  | ok s₃ =>
  conv => lhs; lhs; whnf
  cases c₃ : chainAt "the second chain" ft b₃ s₃ v₃ with
  | error m =>
    refine ⟨fun h => ?_, ?_⟩
    · cases h
    · rintro ⟨-, -, -, -, -, ha, hb, ⟨t, ht, hc⟩, -⟩
      cases ha
      cases hb
      rw [h₃] at ht
      cases ht
      rw [c₃] at hc
      cases hc
  | ok a₃ =>
  conv => lhs; lhs; whnf
  cases hf : fin a₁ a₂ a₃ with
  | false =>
    refine ⟨fun h => ?_, ?_⟩
    · cases h
    · rintro ⟨-, -, -, -, -, ha, hb, ⟨t, ht, hc⟩, hn⟩
      cases ha
      cases hb
      rw [h₃] at ht
      cases ht
      rw [c₃] at hc
      cases hc
      rw [hf] at hn
      cases hn
  | true =>
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨s₃, h₃, c₃⟩, hf⟩
    · rintro ⟨-, -, -, -, -, ha, hb, ⟨t, ht, hc⟩, -⟩
      cases ha
      cases hb
      rw [h₃] at ht
      cases ht
      rw [c₃] at hc
      cases hc
      rfl

/-- The refusal on the plan has no words just where the tests on the plan pass. -/
theorem planWord_none {Xi : Type} (F : FileDescription Xi) : F.planWord = none ↔ F.planOk = true := by
  unfold FileDescription.planWord
  cases F.planOk with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h
  | true =>
    constructor
    · intro _
      rfl
    · intro _
      rfl

theorem descRun₁_some {Xi : Type} (F : FileDescription Xi) (x : Xi) (v : Fmt.View) (e : F.S₁) :
    descRun₁ F x v = some (F.pub x, e) ↔ viewWordsBelowPrime v = true ∧
      chainAt "the first chain" 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v) = .ok e := by
  unfold descRun₁
  cases viewWordsBelowPrime v with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.1
  | true =>
  cases chainAt "the first chain" 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v) with
  | error m =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2
  | ok a =>
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨-, h⟩
      cases h
      rfl

theorem descRun₂_some {Xi : Type} (F : FileDescription Xi) (p : F.XiPub) (e₁ : F.S₁) (v : Fmt.View)
    (e : F.S₂) :
    descRun₂ F (p, e₁) v = some (p, e₁, e) ↔ viewWordsBelowPrime v = true ∧
      chainAt "the shared chain" 0 F.shared.blocksInOrder (F.start₂ p) v = .ok e := by
  unfold descRun₂
  cases viewWordsBelowPrime v with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.1
  | true =>
  show ((chainAt "the shared chain" 0 F.shared.blocksInOrder (F.start₂ p) v).toOption.map
    fun s => (p, e₁, s)) = some (p, e₁, e) ↔ _
  cases chainAt "the shared chain" 0 F.shared.blocksInOrder (F.start₂ p) v with
  | error m =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.2
  | ok a =>
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨-, h⟩
      cases h
      rfl

theorem runEndIs : RunEndIs := by
  intro Xi F x v₁ v₂ v₃ e₁ e₂ e₃
  unfold FileDescription.runEnd
  rw [runCore_ok, planWord_none, descRun₁_some, descRun₂_some]
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h, i⟩
    exact ⟨a, b, ⟨c, f⟩, ⟨d, g⟩, e, h, i⟩
  · rintro ⟨a, b, ⟨c, f⟩, ⟨d, g⟩, e, h, i⟩
    exact ⟨a, b, c, d, e, f, g, h, i⟩

theorem runGivesRow : RunGivesRow := by
  intro Xi F x v₁ v₂ v₃ h
  unfold FileDescription.run at h
  cases hr : F.runEnd x v₁ v₂ v₃ with
  | error m =>
    rw [hr] at h
    cases h
  | ok t =>
    obtain ⟨e₁, e₂, e₃⟩ := t
    obtain ⟨-, -, h₁, h₂, h₃, ⟨s₃, hs, hc⟩, -⟩ := (runEndIs Xi F x v₁ v₂ v₃ e₁ e₂ e₃).1 hr
    unfold runRow
    simp only [h₁, h₂]
    show (viewWordsBelowPrime v₃ && ((F.start₃ (F.pub x) e₁ e₂).toOption.bind fun s =>
                  (chainAt "the second chain" F.lastChainFirstTreeNumber F.second.blocksInOrder s v₃).toOption).isSome) = true
    rw [h₃, hs]
    show (true && ((chainAt "the second chain" F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ v₃).toOption).isSome)
      = true
    rw [hc]
    rfl

end VerifiableInference.Desc.Sound
