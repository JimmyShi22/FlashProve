-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Hom.lean: two tools for code that is written once over a variable monad and read in several
monads: a morphism of monads, and a count of questions.

Definitions and two statements (`Run.Spec.hom_foldlM`, `Run.Spec.cost_foldlM`); the proofs are in
Run/HomProofs.lean. Generic; no Mathlib; no format occurs here.

Why: the rules of a format that hash are written once, over a variable monad m, with the hash as a
parameter h : .. → m ByteArray. At m := Id and h := the real hash the code can be evaluated. At m :=
the monad of trees of queries (oracle computations: `OComp`, ZKCP/Defs.lean) and h := "ask" the same
code is the tree that can be part of a verifier. To connect the two one needs: "the tree, run at an
oracle f, gives what the code gives at Id with f". Lean has no free theorem for that; it is one
induction for each function, and always the same one: a morphism of monads passes through pure,
bind, if, match and structural recursion.

Main names:
  `Hom m n`: a morphism of monads. No law of monads is asked of m or n.
  `Cost m`: a count of questions: le x t ("x asks at most t"), with: pure asks at most 0; bind: the
    sum; a larger number is a bound too.
  `Spec.hom_foldlM`, `Spec.cost_foldlM`: a morphism, and a count, through `List.foldlM`, the loop
    over a list of Lean's own library.

Limits: the format's own functions loop by structural recursion alone (read in their files); their
statements on morphisms and on counts are in Run/HomFmt.lean and Run/CostFmt.lean.
This file does not say that a given map is a morphism, or that a given predicate is a count. For
the monad of trees of queries see Run/OCompM.lean; the records are in Run/OCompHom.lean.
`Cost m` is any predicate with the three rules; the predicate that is always true is one: what a
statement "c.le x t" says hangs on the instance c alone.
-/

set_option autoImplicit false

namespace Run

/-- A morphism of monads from m to n: `app` commutes with `pure` and with `>>=`. -/
structure Hom (m n : Type → Type) [Monad m] [Monad n] where
  app : {α : Type} → m α → n α
  app_pure : ∀ {α : Type} (a : α), app (pure a : m α) = pure a
  app_bind : ∀ {α β : Type} (x : m α) (g : α → m β), app (x >>= g) = app x >>= fun a => app (g a)

/-- The hash h, read through the morphism. -/
abbrev Hom.on {m n : Type → Type} [Monad m] [Monad n] (φ : Hom m n)
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) :
    Nat → Nat → Nat → ByteArray → ByteArray → n ByteArray :=
  fun number tree index start bytes => φ.app (h number tree index start bytes)

/-- A count of questions: `le x t` is read "x asks at most t". It is any predicate with the three
rules below: see the head, Limits. -/
structure Cost (m : Type → Type) [Monad m] where
  le : {α : Type} → m α → Nat → Prop
  le_pure : ∀ {α : Type} (a : α), le (pure a : m α) 0
  le_bind : ∀ {α β : Type} (x : m α) (g : α → m β) (s t : Nat),
    le x s → (∀ a, le (g a) t) → le (x >>= g) (s + t)
  le_mono : ∀ {α : Type} (x : m α) (s t : Nat), le x s → s ≤ t → le x t

namespace Spec

/-- States: a morphism of monads passes through `List.foldlM`. -/
def hom_foldlM : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n) (α β : Type)
      (g : β → α → m β) (l : List α) (b : β),
    φ.app (l.foldlM g b) = l.foldlM (fun b a => φ.app (g b a)) b

/-- States: if every step `g b a` asks at most t, then `l.foldlM g b` asks at most l.length * t, in
the sense of any count c. -/
def cost_foldlM : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : Cost m) (α β : Type) (g : β → α → m β) (t : Nat),
    (∀ b a, c.le (g b a) t) → ∀ (l : List α) (b : β), c.le (l.foldlM g b) (l.length * t)

end Spec

end Run
