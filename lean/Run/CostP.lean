-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CostP.lean: a count of questions with a condition on what comes out.

Why. Run/Hom.lean's `Cost m` has the rule "bind: the sum" in the form: x asks at most s, and g a
asks at most t for all a. That is too weak where the number of questions of the second step depends
on what the first step puts out. In the walk up a tree the list of vertices of the next depth comes
out of the monad, and the next depth asks at most one question for each of them: for an arbitrary
list there is no bound; for the lists that really come out (no longer than the one before) there
is. Generic; no Mathlib; no format occurs here.

1. What the file contains.
   `CostP m`: le x t P is read "x asks at most t, and whatever it puts out has P". Its rules: pure
      a asks at most 0, if P a; a bind asks at most the sum of its two steps, the second step
      counted only at the a with P; a larger number and a weaker condition hold too.
   `CostP.cost`: c.cost is the count without a condition (P := true): a `Cost m` (the three rules
      are proved in the definition).

2. What is checked when the file compiles. Only the types and the three rules of `CostP.cost`.

3. Theorem stated. `Spec.costP_cost`: c.cost.le x t ↔ c.le x t at the condition that always holds.
   Its proof is in Run/CostPProofs.lean.

4. What is not claimed. It is not claimed that a given predicate is such a count: for the monad of
   trees of queries that is another file's matter (`qp`, Run/OCompCostP.lean). `CostP m` is any
   predicate with the three rules; the predicate that is always true is one: what "c.le x t P" says
   depends on the instance c alone.
-/
import Run.Hom

set_option autoImplicit false

namespace Run

/-- A count of questions with a condition on what comes out: `le x t P` is read "x asks at most t,
and whatever it puts out has P". It is any predicate with the three rules below: see the head, 4. -/
structure CostP (m : Type → Type) [Monad m] where
  le : {α : Type} → m α → Nat → (α → Prop) → Prop
  le_pure : ∀ {α : Type} (a : α) (P : α → Prop), P a → le (pure a : m α) 0 P
  le_bind : ∀ {α β : Type} (x : m α) (g : α → m β) (s t : Nat) (P : α → Prop) (Q : β → Prop),
    le x s P → (∀ a, P a → le (g a) t Q) → le (x >>= g) (s + t) Q
  le_mono : ∀ {α : Type} (x : m α) (s t : Nat) (P Q : α → Prop),
    le x s P → s ≤ t → (∀ a, P a → Q a) → le x t Q

/-- The count without a condition: `c.le` at the condition that always holds. -/
def CostP.cost {m : Type → Type} [Monad m] (c : CostP m) : Cost m where
  le := fun x t => c.le x t fun _ => True
  le_pure := fun a => c.le_pure a _ trivial
  le_bind := fun x g s t hx hg => c.le_bind x g s t _ _ hx fun a _ => hg a
  le_mono := fun x s t hx hst => c.le_mono x s t _ _ hx hst fun _ h => h

/-- States what the count without a condition says. -/
def Spec.costP_cost : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : CostP m) (α : Type) (x : m α) (t : Nat),
    c.cost.le x t ↔ c.le x t fun _ => True

end Run
