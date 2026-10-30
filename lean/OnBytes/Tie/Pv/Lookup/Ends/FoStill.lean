-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStill.lean.
Routines of the byte-level verifier that turn neither the state of the sub-proof nor the context.

Many routines of a sub-proof's check only compute a form from public numbers and from what the state
holds: they test, they look up, they refuse, but if they return, state and context are as before.
This file gives that property a name and the laws by which it passes through the ways of putting
routines together.

Defines:
  StillB b: if the block b returns, the context is as it was.
  Still x: if the routine x returns, the state of the sub-proof and the context are as they were.
States: the laws for pure, bind, a lifted block, reading the state, a choice, a loop over a range or
a list; that the blocks mustAs, getAs, held, refuse keep the context (StillB); that uEnt is still.
Not said: what a still routine returns, or that it returns.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEv
import OnBytes.Model.Head

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- If the block returns, the context is as it was. -/
def StillB {α : Type} (b : Blk α) : Prop := ∀ c r, b c = .ok r → r.2 = c

/-- If the routine returns, state and context are as they were. -/
def Still {α : Type} (x : SubM α) : Prop := ∀ F c r, x F c = .ok r → r.1.2 = F ∧ r.2 = c

section
variable {α β : Type}

theorem StillB.pure (a : α) : StillB (Pure.pure a : Blk α) := by
  intro c r h
  have e : (a, c) = r := Except.ok.inj h
  rw [← e]

theorem StillB.refuse (name : String) : StillB (refuse name : Blk α) := by
  intro c r h
  have e : (Except.error { name := name } : Except Failure (α × Ctx)) = .ok r := h
  cases e

theorem StillB.mustAs (name : String) (b : Bool) : StillB (mustAs name b) := by
  unfold OnBytes.Model.mustAs
  cases b
  · exact StillB.refuse name
  · exact StillB.pure ()

theorem StillB.getAs (name : String) (x : Option α) : StillB (Head.getAs name x) := by
  unfold Head.getAs
  cases x
  · exact StillB.refuse name
  · exact StillB.pure _

theorem StillB.held (x : Except String α) : StillB (Head.held x) := by
  unfold Head.held
  cases x
  · exact StillB.refuse _
  · exact StillB.pure _

theorem Still.pure (a : α) : Still (Pure.pure a : SubM α) := by
  intro F c r h
  rw [(pure_ok a F c r).1 h]
  exact ⟨rfl, rfl⟩

theorem Still.bind {x : SubM α} {f : α → SubM β} (hx : Still x) (hf : ∀ a, Still (f a)) :
    Still (x >>= f) := by
  intro F c r h
  obtain ⟨a, G, c1, h1, h2⟩ := (bind_ok x f F c r).1 h
  obtain ⟨e1, e2⟩ := hx F c _ h1
  obtain ⟨e3, e4⟩ := hf a G c1 r h2
  exact ⟨e3.trans e1, e4.trans e2⟩

theorem Still.lift {b : Blk α} (hb : StillB b) : Still (StateT.lift b : SubM α) := by
  intro F c r h
  obtain ⟨a, c1, h1, rfl⟩ := (lift_ok b F c r).1 h
  exact ⟨rfl, hb c _ h1⟩

theorem Still.liftM {b : Blk α} (hb : StillB b) : Still (liftM b : SubM α) := Still.lift hb

theorem Still.get : Still (MonadState.get : SubM Fork) := by
  intro F c r h
  have e : ((F, F), c) = r := Except.ok.inj h
  rw [← e]
  exact ⟨rfl, rfl⟩

theorem Still.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : Still x) (hy : Still y) :
    Still (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem Still.forInL {γ : Type} (f : γ → β → SubM (ForInStep β)) (hf : ∀ a b, Still (f a b)) :
    ∀ (l : List γ) (b : β), Still (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact Still.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Still.bind (hf a b) fun s => ?_
    cases s
    · exact Still.pure _
    · exact Still.forInL f hf l _

theorem Still.forInR (f : ℕ → β → SubM (ForInStep β)) (hf : ∀ a b, Still (f a b))
    (r : Std.Legacy.Range) (b : β) : Still (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Still.forInL f hf _ b

end

theorem still_uEnt (t x : ℕ) : Still (uEnt t x) := by
  unfold uEnt
  exact Still.bind Still.get fun _ => Still.bind (Still.lift (StillB.mustAs _ _)) fun _ =>
    Still.pure _

end Fo
