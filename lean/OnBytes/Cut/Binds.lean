-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Cut/Binds.lean: a routine that is made of two steps and returns, cut between the steps, for
the routines inside a link. For proofs only; the program does not import this file.

A block binds in `Blk`; of that bind the library has `Blk.yields_bind`
(OnBytes/Iop/GroundLaws.lean), and OnBytes/Cut/Run.lean goes on from it. A routine of a sub-proof
binds in `SubM`, which is `Blk` with a state more; a routine of a link in `LinkM`, which is `SubM`
with a state more.
  `bindS`, `bindL`: where `x >>= f` returns from given states, x has returned from these states, and
    `f` at what x returned has returned from the states that x has left.
  `liftB_ok`, `liftS_ok`: a block, or a routine of a sub-proof, lifted into a link's routine: where
    it returns, the block or routine has returned, and the states that it does not know are as
    before.
  `mapL`: where `g <$> x` returns, x has returned with the same states, and the value is g's image.
The value and the states between stand under "there are", each with the equation that gives it.
-/
import OnBytes.Model.Trees

set_option autoImplicit false

namespace OnBytes.Cut

open OnBytes OnBytes.Model

/-- Two steps of a link's routine. -/
theorem bindL {α β : Type} {x : LinkM α} {f : α → LinkM β} {L : LinkCtx} {F : Fork} {c : Ctx}
    {r : ((β × LinkCtx) × Fork) × Ctx} (h : (x >>= f) L F c = .ok r) :
    ∃ a L' F' c', x L F c = .ok (((a, L'), F'), c') ∧ f a L' F' c' = .ok r := by
  cases hx : x L F c with
  | error e =>
    simp [bind, StateT.bind, Except.bind, hx] at h
  | ok v =>
    obtain ⟨⟨⟨a, L'⟩, F'⟩, c'⟩ := v
    refine ⟨a, L', F', c', rfl, ?_⟩
    simpa [bind, StateT.bind, Except.bind, hx] using h

/-- Two steps of a sub-proof's routine. -/
theorem bindS {α β : Type} {x : SubM α} {f : α → SubM β} {F : Fork} {c : Ctx}
    {r : (β × Fork) × Ctx} (h : (x >>= f) F c = .ok r) :
    ∃ a F' c', x F c = .ok ((a, F'), c') ∧ f a F' c' = .ok r := by
  cases hx : x F c with
  | error e =>
    simp [bind, StateT.bind, Except.bind, hx] at h
  | ok v =>
    obtain ⟨⟨a, F'⟩, c'⟩ := v
    refine ⟨a, F', c', rfl, ?_⟩
    simpa [bind, StateT.bind, Except.bind, hx] using h

/-- A block, lifted into a link's routine, that returns. -/
theorem liftB_ok {α : Type} {b : Blk α} {L : LinkCtx} {F : Fork} {c : Ctx}
    {r : ((α × LinkCtx) × Fork) × Ctx} (h : (liftM b : LinkM α) L F c = .ok r) :
    ∃ a c', b c = .ok (a, c') ∧ r = (((a, L), F), c') := by
  cases hb : b c with
  | error e =>
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind, Except.bind,
      hb] at h
  | ok v =>
    obtain ⟨a, c'⟩ := v
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind, Except.bind,
      hb, pure, StateT.pure, Except.pure] at h
    exact ⟨a, c', rfl, h.symm⟩

/-- A sub-proof's routine, lifted into a link's routine, that returns. -/
theorem liftS_ok {α : Type} {x : SubM α} {L : LinkCtx} {F : Fork} {c : Ctx}
    {r : ((α × LinkCtx) × Fork) × Ctx} (h : (liftM x : LinkM α) L F c = .ok r) :
    ∃ a F' c', x F c = .ok ((a, F'), c') ∧ r = (((a, L), F'), c') := by
  cases hx : x F c with
  | error e =>
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind, Except.bind,
      hx] at h
  | ok v =>
    obtain ⟨⟨a, F'⟩, c'⟩ := v
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind, Except.bind,
      hx, pure, StateT.pure, Except.pure] at h
    exact ⟨a, F', c', rfl, h.symm⟩

/-- A link's routine under `g <$> ·` that returns: the routine has returned, with the same states,
and the value is g's image of its value. -/
theorem mapL {α β : Type} {g : α → β} {x : LinkM α} {L : LinkCtx} {F : Fork} {c : Ctx}
    {r : ((β × LinkCtx) × Fork) × Ctx} (h : (g <$> x) L F c = .ok r) :
    ∃ a L' F' c', x L F c = .ok (((a, L'), F'), c') ∧ r = (((g a, L'), F'), c') := by
  cases hx : x L F c with
  | error e =>
    simp [Functor.map, StateT.map, bind, StateT.bind, Except.bind, hx] at h
  | ok v =>
    obtain ⟨⟨⟨a, L'⟩, F'⟩, c'⟩ := v
    simp [Functor.map, StateT.map, bind, StateT.bind, Except.bind, hx, pure, StateT.pure,
      Except.pure] at h
    exact ⟨a, L', F', c', rfl, h.symm⟩

end OnBytes.Cut

#print axioms OnBytes.Cut.bindL
#print axioms OnBytes.Cut.bindS
#print axioms OnBytes.Cut.liftB_ok
#print axioms OnBytes.Cut.liftS_ok
#print axioms OnBytes.Cut.mapL
