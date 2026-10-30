-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Model/ExceptHom.lean: a morphism of monads through do-notation inside ExceptT ε m:
a relation kept by pure, bind, throw, the lift from Except ε and the lift from m (which asks a law:
map).
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Key.KeyHom

set_option autoImplicit false

namespace OnBytes.TwoPort.M.Model

variable {m n : Type → Type} [Monad m] [Monad n] {ε : Type}

theorem runE_bind {α β : Type} (x : ExceptT ε m α) (f : α → ExceptT ε m β) :
    (x >>= f).run = x.run >>= fun r =>
      match r with
      | .ok a => (f a).run
      | .error e => pure (.error e) := by
  show x.run >>= ExceptT.bindCont f = _
  refine congrArg _ (funext fun r => ?_)
  cases r <;> rfl

/-- φ carries the run of x to the run of x'. -/
def RelE (φ : Run.Hom m n) {α : Type} (x : ExceptT ε m α) (x' : ExceptT ε n α) : Prop :=
  φ.app x.run = x'.run

variable (φ : Run.Hom m n)

theorem relE_pure {α : Type} (a : α) : RelE φ (pure a : ExceptT ε m α) (pure a) := φ.app_pure _

theorem relE_throw {α : Type} (e : ε) : RelE φ (throw e : ExceptT ε m α) (throw e) :=
  φ.app_pure _

theorem relE_bind {α β : Type} {x : ExceptT ε m α} {x' : ExceptT ε n α}
    {f : α → ExceptT ε m β} {f' : α → ExceptT ε n β} (hx : RelE φ x x')
    (hf : ∀ a, RelE φ (f a) (f' a)) : RelE φ (x >>= f) (x' >>= f') := by
  unfold RelE at hx ⊢
  rw [runE_bind, runE_bind, φ.app_bind, hx]
  refine congrArg _ (funext fun r => ?_)
  cases r with
  | ok a => exact hf a
  | error e => exact φ.app_pure _

/-- Lean's own lift of a pure step in `Except ε`. -/
theorem relE_liftE {α : Type} (x : Except ε α) :
    RelE φ (liftM x : ExceptT ε m α) (liftM x : ExceptT ε n α) := φ.app_pure _

/-- Lean's own lift of a computation in m: it is written with `<$>`, so a law is asked of both. -/
theorem relE_lift [LawfulMonad m] [LawfulMonad n] {α : Type} {x : m α} {x' : n α}
    (hx : φ.app x = x') : RelE φ (liftM x : ExceptT ε m α) (liftM x' : ExceptT ε n α) := by
  subst hx
  show φ.app (Except.ok <$> x) = Except.ok <$> φ.app x
  rw [map_eq_pure_bind, map_eq_pure_bind, φ.app_bind]
  refine congrArg _ (funext fun a => ?_)
  exact φ.app_pure _

theorem relE_mk {α : Type} {x : m (Except ε α)} {x' : n (Except ε α)} (hx : φ.app x = x') :
    RelE φ (ExceptT.mk x) (ExceptT.mk x') := hx

/-- The same for a property that pure has and bind keeps. -/
def OkE (k : Keeps m) {α : Type} (x : ExceptT ε m α) : Prop := k.ok x.run

variable (k : Keeps m)

theorem okE_pure {α : Type} (a : α) : OkE k (pure a : ExceptT ε m α) := k.ok_pure _

theorem okE_throw {α : Type} (e : ε) : OkE k (throw e : ExceptT ε m α) := k.ok_pure _

theorem okE_bind {α β : Type} {x : ExceptT ε m α} {f : α → ExceptT ε m β} (hx : OkE k x)
    (hf : ∀ a, OkE k (f a)) : OkE k (x >>= f) := by
  unfold OkE at hx ⊢
  rw [runE_bind]
  refine k.ok_bind _ _ hx fun r => ?_
  cases r with
  | ok a => exact hf a
  | error e => exact k.ok_pure _

theorem okE_liftE {α : Type} (x : Except ε α) : OkE k (liftM x : ExceptT ε m α) := k.ok_pure _

theorem okE_lift [LawfulMonad m] {α : Type} {x : m α} (hx : k.ok x) :
    OkE k (liftM x : ExceptT ε m α) := by
  show k.ok (Except.ok <$> x)
  rw [map_eq_pure_bind]
  exact k.ok_bind _ _ hx fun _ => k.ok_pure _

end OnBytes.TwoPort.M.Model
