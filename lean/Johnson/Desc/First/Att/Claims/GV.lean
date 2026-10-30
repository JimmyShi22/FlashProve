-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/GV.lean: kind K5, the claims: the rules by which a routine of
Johnson/Desc/First/Att/RunsP.lean is held against a written value and a written list. Such a routine
lives in W α := ReaderT Nat (StateT (Array Aff) Option) α: it knows K, the number of columns of the
array of tables, gathers forms in order, and may refuse.

Main names:
  `GV K r v l`: wherever the routine r returns at K, it returns the value v and has appended just
    the list l to what was gathered.
  The rules: pure, bind (bind0, bind1), never, failure, ite, foldlM (foldlM0), forM, read, lin,
    cast.
The rules mirror Rd, Ad and AdV of OnBytes/Tie/Pv/Lookup/Ends/FoRd.lean, which speak of routines in
a context. These speak of plain functions: no context, no ledger, no run.
Limit: GV says nothing where a routine does not return.

Nothing is claimed on soundness, completeness or hiding.

-/
import Mathlib.Tactic
import Johnson.Desc.First.Att.RunsP

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P.Runs (W)

variable {α β σ : Type} {K : ℕ}

/-- Wherever r returns at K: the value is v, and just l was appended. -/
def GV (K : ℕ) (r : W α) (v : α) (l : List Aff) : Prop :=
  ∀ (acc : Array Aff) (a : α) (acc' : Array Aff), r K acc = some (a, acc') → a = v ∧ acc' = acc ++ l.toArray

theorem GV.pure (v : α) : GV K (Pure.pure v : W α) v [] := by
  intro acc a acc' h
  simp only [Pure.pure, ReaderT.pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, by simp [h.2]⟩

theorem GV.bind {r : W α} {k : α → W β} {v : α} {w : β} {l₁ l₂ : List Aff}
    (h1 : GV K r v l₁) (h2 : GV K (k v) w l₂) : GV K (r >>= k) w (l₁ ++ l₂) := by
  intro acc b acc' h
  simp only [Bind.bind, ReaderT.bind, StateT.bind] at h
  cases hr : r K acc with
  | none => simp [hr] at h
  | some x =>
    obtain ⟨a, acc1⟩ := x
    simp only [hr] at h
    obtain ⟨rfl, rfl⟩ := h1 acc a acc1 hr
    obtain ⟨rfl, rfl⟩ := h2 _ b acc' h
    exact ⟨rfl, by simp [Array.append_assoc]⟩

/-- A routine that never returns meets every value and list. -/
theorem GV.never {r : W α} (h : ∀ acc, r K acc = none) (v : α) (l : List Aff) : GV K r v l := by
  intro acc a acc' hr
  simp [h acc] at hr

theorem GV.ite {p : Prop} [Decidable p] {x y : W α} {v w : α} {l m : List Aff}
    (hx : GV K x v l) (hy : GV K y w m) :
    GV K (if p then x else y) (if p then v else w) (if p then l else m) := by
  split <;> assumption

theorem GV.foldlM (f : σ → α → W σ) (g : σ → α → σ) (L : α → List Aff)
    (hf : ∀ s a, GV K (f s a) (g s a) (L a)) :
    ∀ (xs : List α) (s : σ), GV K (xs.foldlM f s) (xs.foldl g s) (xs.flatMap L)
  | [], s => by simpa using GV.pure (K := K) s
  | a :: xs, s => by
    simp only [List.foldlM_cons, List.foldl_cons, List.flatMap_cons]
    exact GV.bind (hf s a) (GV.foldlM f g L hf xs (g s a))

theorem GV.forM (f : α → W PUnit) (L : α → List Aff) (hf : ∀ a, GV K (f a) () (L a)) :
    ∀ xs : List α, GV K (xs.forM f) () (xs.flatMap L)
  | [] => by simpa using GV.pure (K := K) ()
  | a :: xs => by
    simp only [List.flatMap_cons]
    exact GV.bind (hf a) (GV.forM f L hf xs)

/-- The first gathers nothing. -/
theorem GV.bind0 {r : W α} {k : α → W β} {v : α} {w : β} {l : List Aff}
    (h1 : GV K r v []) (h2 : GV K (k v) w l) : GV K (r >>= k) w l := by
  simpa only [List.nil_append] using GV.bind h1 h2

/-- The second gathers nothing. -/
theorem GV.bind1 {r : W α} {k : α → W β} {v : α} {w : β} {l : List Aff}
    (h1 : GV K r v l) (h2 : GV K (k v) w []) : GV K (r >>= k) w l := by
  simpa only [List.append_nil] using GV.bind h1 h2

theorem GV.foldlM0 (f : σ → α → W σ) (g : σ → α → σ) (hf : ∀ s a, GV K (f s a) (g s a) []) :
    ∀ (xs : List α) (s : σ), GV K (xs.foldlM f s) (xs.foldl g s) []
  | [], s => by simpa only [List.foldlM_nil, List.foldl_nil] using GV.pure (K := K) s
  | a :: xs, s => by
    simp only [List.foldlM_cons, List.foldl_cons]
    exact GV.bind0 (hf s a) (GV.foldlM0 f g hf xs (g s a))

theorem GV.read : GV K (read : W ℕ) K [] := by
  intro acc a acc' h
  have h' : (some (K, acc) : Option (ℕ × Array Aff)) = some (a, acc') := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  exact ⟨h'.1.symm, by simp [h'.2]⟩

theorem GV.lin (f : Aff) : GV K (VerifiableInference.Desc.First.Att.P.Runs.W.lin f) () [f] := by
  intro acc a acc' h
  have h' : (some ((), acc.push f) : Option (Unit × Array Aff)) = some (a, acc') := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  refine ⟨rfl, ?_⟩
  rw [← h'.2]
  simp

theorem GV.failure (v : α) (l : List Aff) : GV K (failure : W α) v l :=
  GV.never (fun _ => rfl) v l

theorem GV.cast {r : W α} {v v' : α} {l l' : List Aff} (h : GV K r v l) (hv : v = v') (hl : l = l') : GV K r v' l' := by
  subst hv; subst hl; exact h

end K5Law
