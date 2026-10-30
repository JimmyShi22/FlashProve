-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachInv.lean: THE ONE INDUCTION ALONG "REACHED" (Reach.lean; ReachThree.lean):
a family of conditions, border by border, that holds at the first state and that every
sub-protocol's own accepting step hands on holds at every reached state. For whoever pays a fact on
the verifier's state with the whole chain as its span ("∀ k a, Rch k a → the fact").

  stepYes_decide    an accepting step is an accepting decision, at some rounds and groups of columns
  Reach.inv, ReachR.inv   THE INDUCTION. The step's premise has in hand: the state in front is
                    itself reached; which sub-protocol stands at number k; its accepting step
  rchAt_inv, rchAt_inv_below   at an IOP as written in Lean, at its first chain: with the
                    sub-protocols' own accepting steps in hand; with the wrapped ones'

No soundness statement.

-/
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound

section
variable {S Cl P : Type}

theorem stepYes_decide {ft : ℕ} {b : Block S Cl} {s s' : S} (h : StepYes ft b s s') :
    ∃ rs gs, b.decide s rs gs = .ok s' := by
  obtain ⟨R, c, _, e⟩ := h
  exact ⟨_, _, ((step_ok_iff ft b s s' R c c.length).1 e).2.2.2⟩

/-- **THE INDUCTION.** -/
theorem Reach.inv {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {Inv : ℕ → P × S → Prop}
    (h0 : ∀ z, Inv 0 (z, start z))
    (hs : ∀ k z s s' b, Reach ft bs start k (z, s) → bs[k]? = some b → StepYes ft b s s' →
      Inv k (z, s) → Inv (k + 1) (z, s')) {k : ℕ} {a : P × S} (h : Reach ft bs start k a) :
    Inv k a := by
  induction h with
  | zero z => exact h0 z
  | succ hr hb hy ih => exact hs _ _ _ _ _ hr hb hy ih

theorem ReachR.inv {ft : ℕ} {bs : List (Block S Cl)} {Start : P → S → Prop}
    {Inv : ℕ → P × S → Prop} (h0 : ∀ z s, Start z s → Inv 0 (z, s))
    (hs : ∀ k z s s' b, ReachR ft bs Start k (z, s) → bs[k]? = some b → StepYes ft b s s' →
      Inv k (z, s) → Inv (k + 1) (z, s')) {k : ℕ} {a : P × S} (h : ReachR ft bs Start k a) :
    Inv k a := by
  induction h with
  | zero e => exact h0 _ _ e
  | succ hr hb hy ih => exact hs _ _ _ _ _ hr hb hy ih

end

/-- At an IOP as written in Lean, at its first chain. -/
theorem rchAt_inv {Xi Str : Type} {F : FileDescription Xi} {Inv : ℕ → F.XiPub × F.S₁ → Prop}
    (h0 : ∀ z, Inv 0 (z, F.start₁ z))
    (hs : ∀ k z s s' b, Reach 0 F.first.blocksInOrder F.start₁ k (z, s) → F.first.blocksInOrder[k]? = some b →
      StepYes 0 b s s' → Inv k (z, s) → Inv (k + 1) (z, s')) {k : ℕ}
    {a : (F.XiPub × F.S₁) × Str} (h : RchAt F k a) : Inv k a.1 :=
  Reach.inv h0 hs (rchAt_raw h)

/-- The same with the wrapped sub-protocols' accepting steps in hand: for a fact that hangs on
"every word shown is below the prime". -/
theorem rchAt_inv_below {Xi Str : Type} {F : FileDescription Xi} {Inv : ℕ → F.XiPub × F.S₁ → Prop}
    (h0 : ∀ z, Inv 0 (z, F.start₁ z))
    (hs : ∀ k z s s' b, Reach 0 (F.first.blocksInOrder.map below) F.start₁ k (z, s) →
      F.first.blocksInOrder[k]? = some b → StepYes 0 (below b) s s' → Inv k (z, s) → Inv (k + 1) (z, s'))
    {k : ℕ} {a : (F.XiPub × F.S₁) × Str} (h : RchAt F k a) : Inv k a.1 :=
  Reach.inv (bs := F.first.blocksInOrder.map below) h0 (fun k z s s' b hr hb hy ih => by
             rw [List.getElem?_map] at hb
             cases hB : F.first.blocksInOrder[k]? with
             | none => rw [hB] at hb; cases hb
             | some B =>
               rw [hB] at hb
               obtain rfl : below B = b := Option.some.inj hb
               exact hs k z s s' B hr hB hy ih) h

#print axioms Reach.inv
#print axioms rchAt_inv
#print axioms rchAt_inv_below

end Johnson.Desc.First.Walk.Tied
