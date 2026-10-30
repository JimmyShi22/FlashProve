-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoGives.lean.
Routines of a sub-proof whose returned value does not depend on the run.

Many routines of the byte-level verifier add claims, and so turn the state, while the value that
they return is a closed term of their arguments. Returns x a says: every run of x that returns,
returns a.

States:
  Returns; gives_pure, gives_bind (the value of the first routine is known), gives_then (the second
    routine's value does not depend on the first's), gives_ite, gives_foldlM (a loop over a list is
    the plain fold of the steps' values), gives_foldlMA (the same over an array).
Not claimed: that a run returns; what a run does to the state.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- Every run of x that returns, returns a. -/
def Returns {α : Type} (x : SubM α) (a : α) : Prop :=
  ∀ (F G : Fork) (c c' : Ctx) (r : α), x F c = .ok ((r, G), c') → r = a

section
variable {α β σ : Type}

theorem gives_pure (a : α) : Returns (pure a : SubM α) a := by
  intro F G c c' r h
  exact congrArg (fun x : (α × Fork) × Ctx => x.1.1) ((pure_ok _ _ _ _).1 h)

theorem gives_bind {x : SubM β} {f : β → SubM α} {b : β} {a : α} (hx : Returns x b)
    (hf : Returns (f b) a) : Returns (x >>= f) a := by
  intro F G c c' r h
  obtain ⟨b', F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 h
  obtain rfl := hx _ _ _ _ _ h1
  exact hf _ _ _ _ _ h2

theorem gives_then {x : SubM β} {f : β → SubM α} {a : α} (hf : ∀ b, Returns (f b) a) :
    Returns (x >>= f) a := by
  intro F G c c' r h
  obtain ⟨b', F1, c1, _, h2⟩ := (bind_ok _ _ _ _ _).1 h
  exact hf b' _ _ _ _ _ h2

theorem gives_ite {p : Prop} [Decidable p] {x y : SubM α} {a b : α} (hx : Returns x a)
    (hy : Returns y b) : Returns (if p then x else y) (if p then a else b) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp]
    exact hx
  · rw [if_neg hp, if_neg hp]
    exact hy

theorem gives_foldlM (f : σ → α → SubM σ) (p : σ → α → σ) (h : ∀ s a, Returns (f s a) (p s a)) :
    ∀ (l : List α) (s : σ), Returns (l.foldlM f s) (l.foldl p s)
  | [], s => gives_pure s
  | a :: l, s => by
    rw [List.foldlM_cons, List.foldl_cons]
    exact gives_bind (h s a) (gives_foldlM f p h l (p s a))

theorem gives_foldlMA (f : σ → α → SubM σ) (p : σ → α → σ) (h : ∀ s a, Returns (f s a) (p s a))
    (l : Array α) (s : σ) : Returns (l.foldlM f s) (l.toList.foldl p s) := by
  rw [← Array.foldlM_toList]
  exact gives_foldlM f p h l.toList s

end
end Fo
