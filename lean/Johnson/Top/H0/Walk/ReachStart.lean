-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachStart.lean: from "reached from ONE first state" to "reached, with the first
state as a relation" (ReachR, ReachThree.lean): for whoever shows a member of RchAt₃ off an
accepting run: the second chain's first state is what start₃ has accepted, and the run's own fold
goes on from it.

  reachR_of_const   Reach ft bs (fun _ => s₀) k a → Start a.1 s₀ → ReachR ft bs Start k a
  reachR_of_fold    the same from the fold: k ≤ bs.length, Start z s₀ and
                    foldBlocks ft (bs.take k) s₀ rs cols = .ok (t, [], []) give
                    ReachR ft bs Start k (z, t)
  rchAt₃_of_fold    so a member of RchAt₃: from start₃'s accepting value s₀, a fold of the first k
                    wrapped sub-protocols of the second chain from s₀, and the two reached ends

No soundness statement.

-/
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.Sound

section
variable {S Cl P : Type}

/-- **Reached from one first state that Start relates to the public part.** -/
theorem reachR_of_const {ft : ℕ} {bs : List (Block S Cl)} {Start : P → S → Prop} {s₀ : S} {k : ℕ}
    {a : P × S} (h : Reach ft bs (fun _ => s₀) k a) (hs : Start a.1 s₀) :
    ReachR ft bs Start k a := by
  induction h with
  | zero z => exact ReachR.zero hs
  | succ _ hb hy ih => exact ReachR.succ (ih hs) hb hy

/-- The same from the fold. -/
theorem reachR_of_fold {ft : ℕ} {bs : List (Block S Cl)} {Start : P → S → Prop} {s₀ t : S} {k : ℕ}
    {z : P} (hk : k ≤ bs.length) (hs : Start z s₀) {rs : List Fmt.RoundView}
    {cols : List OpenedColumn}
    (hf : foldBlocks ft (bs.take k) s₀ rs cols = .ok (t, [], [])) :
    ReachR ft bs Start k (z, t) :=
  reachR_of_const (a := (z, t)) ((reach_fold (start := fun _ : P => s₀)).2 ⟨hk, rs, cols, hf⟩) hs

end

/-- **A member of RchAt₃.** -/
theorem rchAt₃_of_fold {Xi Str : Type} {F : FileDescription Xi} {p : F.XiPub × F.S₁ × F.S₂} {s₀ t : F.S₃}
    {k : ℕ} (hk : k ≤ F.second.blocksInOrder.length) (hs : F.start₃ p.1 p.2.1 p.2.2 = .ok s₀)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hf : foldBlocks F.lastChainFirstTreeNumber ((F.second.blocksInOrder.map below).take k) s₀ rs cols = .ok (t, [], []))
    (hE : EndAt₂ F p) (y : Str) : RchAt₃ F k ((p, t), y) :=
  ⟨reachR_of_fold (Start := fun (p : F.XiPub × F.S₁ × F.S₂) s => F.start₃ p.1 p.2.1 p.2.2 = .ok s)
    (by rw [List.length_map]; exact hk) hs hf, hE⟩

#print axioms reachR_of_const
#print axioms reachR_of_fold
#print axioms rchAt₃_of_fold

end Johnson.Desc.First.Walk.Tied
