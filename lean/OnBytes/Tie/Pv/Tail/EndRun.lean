-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndRun.lean: what it says of a routine of a sub-proof (SubM,
OnBytes/Model/Hide.lean)
that it has returned a value: laws for a bind, a lifted call, a named condition, and the two calls
that read the state or an optional value.

Statements and proofs. The routines are applied to a state and a context, as in
OnBytes/Model/HideLaws.lean. OnBytes/Iop/GroundLaws.lean has the like for Blk.
Main names:
  `bind_ok`, `lift_ok`, `mustAs_ok`, `ask_ok`, `get_ok`.
Limits: nothing on a run that fails.

-/
import OnBytes.Model.Tail
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

/-! ## Runs of SubM: what a success says -/

theorem bind_ok {α β : Type} (x : SubM α) (f : α → SubM β) (F : Fork) (c : Ctx)
    (r : (β × Fork) × Ctx) :
    (x >>= f) F c = .ok r ↔ ∃ a F1 c1, x F c = .ok ((a, F1), c1) ∧ f a F1 c1 = .ok r := by
  show (StateT.bind x f) F c = .ok r ↔ _
  simp only [StateT.bind]
  show (StateT.bind (x F) _) c = .ok r ↔ _
  simp only [StateT.bind]
  show Except.bind (x F c) _ = .ok r ↔ _
  cases h : x F c with
  | error e => simp [Except.bind]
  | ok v =>
    obtain ⟨⟨a, F1⟩, c1⟩ := v
    simp [Except.bind]

theorem lift_ok {α : Type} (b : Blk α) (F G : Fork) (c c' : Ctx) (a : α) :
    (liftM b : SubM α) F c = .ok ((a, G), c') ↔ b c = .ok (a, c') ∧ G = F := by
  show (StateT.lift b : SubM α) F c = .ok ((a, G), c') ↔ _
  simp only [StateT.lift]
  show (StateT.bind b _) c = .ok ((a, G), c') ↔ _
  simp only [StateT.bind]
  show Except.bind (b c) _ = .ok ((a, G), c') ↔ _
  cases h : b c with
  | error e => simp [Except.bind]
  | ok v =>
    obtain ⟨a1, c1⟩ := v
    simp only [Except.bind]
    show (Except.ok ((a1, F), c1) : Except Failure _) = .ok ((a, G), c') ↔ _
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2.symm⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2.symm⟩, h3⟩

theorem mustAs_ok (name : String) (b : Bool) (c c' : Ctx) (u : Unit) :
    mustAs name b c = .ok (u, c') ↔ b = true ∧ c' = c := by
  unfold mustAs
  cases b with
  | true => simp [pure, StateT.pure, Except.pure, eq_comm]
  | false => simp [refuse, Blk.fail]

theorem ask_ok {α : Type} (f : Fork → Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    SubM.ask f F c = .ok ((a, G), c') ↔ f F = some a ∧ G = F ∧ c' = c := by
  simp only [SubM.ask]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, and_assoc]

theorem get_ok {α : Type} (x : Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    SubM.get x F c = .ok ((a, G), c') ↔ x = some a ∧ G = F ∧ c' = c := by
  show (StateT.lift (Blk.get x) : SubM α) F c = _ ↔ _
  have := lift_ok (Blk.get x) F G c c' a
  rw [show (StateT.lift (Blk.get x) : SubM α) = liftM (Blk.get x) from rfl, this]
  cases x with
  | none => simp [Blk.get]
  | some y => simp [Blk.get, eq_comm, and_assoc, and_comm]

end OnBytes.Tie.Pv.Tail.Port
