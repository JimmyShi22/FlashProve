-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/StepKeeps.lean: the fold's rule of Johnson/Desc/FoldKeeps.lean FOR A LAW THAT HOLDS OF
A BLOCK ONLY WHERE ITS TESTS ON THE PLAN PASS AND ITS ROUNDS FIT. A block's decision is called by
its step, which first asks that the rounds fit; and a chain is run only where every block's test on
the plan has passed. So a relation R on the record that a block's STEP keeps, at a plan that passes,
is carried along a fold as one that its decision keeps everywhere. Theorems.

  Steps R b            where b's test on the plan passes, a yes of b's step keeps R.
  steps_of_decides     a block whose decision keeps R.
  step_fit             what a yes of a step holds: the rounds fit, and the decision's yes at the
                       rounds without the sealed digest.
  fold_one             a fold over one block rests on a yes of its step.
  foldBlocks_steps     **the rule.**
What is not claimed. That a chain's run asks every block's test on the plan: that is the file's
decision's own.

-/
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps

variable {S Cl : Type}

/-- Where the block's test on the plan passes, a yes of its step keeps R. -/
def Steps (R : S → S → Prop) (b : Block S Cl) : Prop :=
  b.planOk = true → ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : Nat),
    b.step ft s rs cols = .ok (s', k) → R s s'

/-- A block whose decision keeps R. -/
theorem steps_of_decides {R : S → S → Prop} {b : Block S Cl} (h : Decides R b) : Steps R b := by
  intro _ ft s rs cols s' k hs
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft b s s' rs cols k hs
  exact h _ _ _ _ hd

/-- What a yes of a step holds. -/
theorem step_fit (ft : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (k : Nat) (h : b.step ft s rs cols = .ok (s', k)) :
    roundsFit b.rounds rs = true ∧ ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  unfold Block.step at h
  obtain ⟨_, h1, h⟩ := ebind_ok h
  obtain ⟨_, _, h⟩ := ebind_ok h
  obtain ⟨t, h3, h⟩ := ebind_ok h
  have e : t = s' := (Prod.mk.inj (Except.ok.inj h)).1
  refine ⟨?_, _, e ▸ h3⟩
  unfold need at h1
  split at h1
  · assumption
  · cases h1

/-- A fold over one block rests on a yes of its step. -/
theorem fold_one (ft : Nat) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (r : S × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft [b] s rs cols = .ok r) :
    ∃ rs₀ k, b.step ft s rs₀ cols = .ok (r.1, k) := by
  simp only [foldBlocks] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i s' k hs
      cases h
      exact ⟨_, k, hs⟩

section rule
variable (R : S → S → Prop) (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)

include hr ht in
/-- **The fold over blocks whose steps keep R, at a plan that passes, keeps R.** -/
theorem foldBlocks_steps (ft : Nat) : ∀ (bs : List (Block S Cl)), (∀ b ∈ bs, Steps R b) →
    (∀ b ∈ bs, b.planOk = true) →
    ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs cols = .ok r → R s r.1 := by
  intro bs
  induction bs with
  | nil =>
    intro _ _ s rs cols r h
    simp only [foldBlocks, Except.ok.injEq] at h
    subst h
    exact hr s
  | cons b l ih =>
    intro hb hp s rs cols r h
    simp only [foldBlocks] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i s' k hs
        exact ht _ _ _ (hb b List.mem_cons_self (hp b List.mem_cons_self) _ _ _ _ _ _ hs)
          (ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))
            (fun x hx => hp x (List.mem_cons_of_mem _ hx)) _ _ _ _ h)

end rule

end VerifiableInference.Desc.Keeps
