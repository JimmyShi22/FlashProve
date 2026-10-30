-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Proof/ReadingHom.lean: a morphism of monads through do-notation inside Reading m:
a relation between a reading over m and one over n, kept by pure, bind, throw and the named steps.
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadHom
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadKeeps

set_option autoImplicit false

namespace OnBytes.TwoPort.M.Proof

open OnBytes.Proof

variable {m n : Type → Type} [Monad m] [Monad n]

/-- The run form of a bind inside `Reading m`. -/
theorem Reading.run_bind {α β : Type} (w : Reading m α) (g : α → Reading m β) (s : Session) :
    ((w >>= g) s).run = (w s).run >>= fun r =>
      match r with
      | .ok p => (g p.1 p.2).run
      | .error e => pure (.error e) := by
  show (w s).run >>= ExceptT.bindCont (fun p => g p.1 p.2) = _
  refine congrArg _ (funext fun r => ?_)
  cases r <;> rfl

/-- φ carries each run of w to the run of w'. -/
def Rel (φ : Run.Hom m n) {α : Type} (w : Reading m α) (w' : Reading n α) : Prop :=
  ∀ s, φ.app (w s).run = (w' s).run

variable (φ : Run.Hom m n)

theorem rel_pure {α : Type} (a : α) : Rel φ (pure a : Reading m α) (pure a) :=
  fun _ => φ.app_pure _

theorem rel_throw {α : Type} (e : String) : Rel φ (throw e : Reading m α) (throw e) := by
  intro s
  show φ.app ((pure (Except.error e) : m (Except String α)) >>=
      ExceptT.bindCont (fun a => (pure (a, s) : ExceptT String m (α × Session)))) =
    ((pure (Except.error e) : n (Except String α)) >>=
      ExceptT.bindCont (fun a => (pure (a, s) : ExceptT String n (α × Session))))
  rw [φ.app_bind, φ.app_pure]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> exact φ.app_pure _

theorem rel_bind {α β : Type} {w : Reading m α} {w' : Reading n α} {g : α → Reading m β}
    {g' : α → Reading n β} (hw : Rel φ w w') (hg : ∀ a, Rel φ (g a) (g' a)) :
    Rel φ (w >>= g) (w' >>= g') := by
  intro s
  rw [Reading.run_bind, Reading.run_bind, φ.app_bind, hw s]
  refine congrArg _ (funext fun r => ?_)
  cases r with
  | ok p => exact hg p.1 p.2
  | error e => exact φ.app_pure _

theorem rel_need {α : Type} (why : String) (x : Option α) :
    Rel φ (need (m := m) why x) (need why x) := RoadHom.app_need φ why x

theorem rel_needM {α : Type} (why : String) {x : m (Option α)} {x' : n (Option α)}
    (hx : φ.app x = x') : Rel φ (needM why x) (needM why x') := by
  subst hx
  exact RoadHom.app_needM φ why x

theorem rel_readNamed (h : HashM m) (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    Rel φ (readNamed h front S b i) (readNamed (φ.on h) front S b i) :=
  RoadHom.app_readNamed φ h front S b i

/-- The same for a property that pure has and bind keeps. -/
def OkR (k : Keeps m) {α : Type} (w : Reading m α) : Prop := ∀ s, k.ok (w s).run

variable (k : Keeps m)

theorem okR_pure {α : Type} (a : α) : OkR k (pure a : Reading m α) := fun _ => k.ok_pure _

theorem okR_throw {α : Type} (e : String) : OkR k (throw e : Reading m α) := by
  intro s
  show k.ok ((pure (Except.error e) : m (Except String α)) >>=
      ExceptT.bindCont (fun a => (pure (a, s) : ExceptT String m (α × Session))))
  refine k.ok_bind _ _ (k.ok_pure _) fun r => ?_
  cases r <;> exact k.ok_pure _

theorem okR_bind {α β : Type} {w : Reading m α} {g : α → Reading m β} (hw : OkR k w)
    (hg : ∀ a, OkR k (g a)) : OkR k (w >>= g) := by
  intro s
  rw [Reading.run_bind]
  refine k.ok_bind _ _ (hw s) fun r => ?_
  cases r with
  | ok p => exact hg p.1 p.2
  | error e => exact k.ok_pure _

end OnBytes.TwoPort.M.Proof
