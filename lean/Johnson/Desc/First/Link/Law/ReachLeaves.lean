-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ReachLeaves.lean: A READING THAT A STRETCH OF SUB-PROTOCOLS LEAVES HAS,
AT A STATE THAT IS REACHED BEHIND THE STRETCH, THE VALUE THAT IT HAD AT A STATE THAT IS REACHED IN
FRONT OF IT, AT THE SAME PUBLIC PART. General in the list of sub-protocols, the start and the
reading. One theorem and a corollary. No text already in the library turns.

  `reach_leaves`: every sub-protocol of the numbers i … i + n - 1 leaves f (`Block.Leaves`) ·
    `Reach ft bs start (i + n) a` ⊢ ∃ s, `Reach ft bs start i (a.1, s)` ∧ f a.2 = f s.
  `reach_carries`: so a value that f has at every state reached at border i it has at every state
    reached at border i + n.
Limits. It says nothing of any reading or sub-protocol. Nothing on soundness.
-/
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (Reach)

theorem reach_leaves {σ Cl P α : Type} (ft : ℕ) (bs : List (Block σ Cl)) (start : P → σ)
    (f : σ → α) (i : ℕ) : ∀ (n : ℕ),
    (∀ j, i ≤ j → j < i + n → ∀ b, bs[j]? = some b → b.Leaves f) →
    ∀ a : P × σ, Reach ft bs start (i + n) a → ∃ s, Reach ft bs start i (a.1, s) ∧ f a.2 = f s
  | 0, _, a, h => ⟨a.2, h, rfl⟩
  | n + 1, hl, a, h => by
    have h' : Reach ft bs start (i + n + 1) a := h
    cases h' with
    | @succ _ z s s' b hr hb hy =>
      obtain ⟨R, c, _, e⟩ := hy
      have hd := ((step_ok_iff ft b s s' R c c.length).1 e).2.2.2
      obtain ⟨t, ht, et⟩ := reach_leaves ft bs start f i n
        (fun j h1 h2 b hb => hl j h1 (by omega) b hb) (z, s) hr
      exact ⟨t, ht, (hl (i + n) (by omega) (by omega) b hb _ _ _ _ hd).trans et⟩

theorem reach_carries {σ Cl P α : Type} (ft : ℕ) (bs : List (Block σ Cl)) (start : P → σ)
    (f : σ → α) (i n : ℕ) (hl : ∀ j, i ≤ j → j < i + n → ∀ b, bs[j]? = some b → b.Leaves f)
    (v : P → α) (h0 : ∀ a, Reach ft bs start i a → f a.2 = v a.1) :
    ∀ a, Reach ft bs start (i + n) a → f a.2 = v a.1 := by
  intro a h
  obtain ⟨s, hs, e⟩ := reach_leaves ft bs start f i n hl a h
  exact e.trans (h0 _ hs)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.reach_leaves
#print axioms VerifiableInference.Desc.LinkJoin.reach_carries
