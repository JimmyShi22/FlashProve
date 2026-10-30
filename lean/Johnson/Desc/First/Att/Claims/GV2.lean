-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/GV2.lean: kind K5, the claims: further rules for `GV`
(Johnson/Desc/First/Att/Claims/GV.lean).

Main names:
  `GV.foldlMmap`: a fold whose state is carried through a map of records. `GV.ite'`: a branch whose
    test is written in two ways. `GV.forInList`: a loop "for … in" over a list. `GV.never_bind`,
    `GV.needSome`, `GV.needNone`, `GV.lin1`.
Nothing of OnBytes is used but the type of a form.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.GV

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P.Runs (W)

variable {α β σ τ : Type} {K : ℕ}

/-- A fold whose state is the image of another record's under φ. -/
theorem GV.foldlMmap (φ : τ → σ) (f : σ → α → W σ) (g : τ → α → τ) (L : α → List Aff)
    (hf : ∀ s a, GV K (f (φ s) a) (φ (g s a)) (L a)) :
    ∀ (xs : List α) (s : τ), GV K (xs.foldlM f (φ s)) (φ (xs.foldl g s)) (xs.flatMap L)
  | [], s => by simpa using GV.pure (K := K) (φ s)
  | a :: xs, s => by
    simp only [List.foldlM_cons, List.foldl_cons, List.flatMap_cons]
    exact GV.bind (hf s a) (GV.foldlMmap φ f g L hf xs (g s a))

/-- A branch whose test is written in two ways. -/
theorem GV.ite' {p q : Prop} [Decidable p] [Decidable q] (hpq : p ↔ q) {x y : W α} {v w : α}
    {l m : List Aff} (hx : GV K x v l) (hy : GV K y w m) :
    GV K (if p then x else y) (if q then v else w) (if q then l else m) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (hpq.1 hp), if_pos (hpq.1 hp)]; exact hx
  · rw [if_neg hp, if_neg (fun h => hp (hpq.2 h)), if_neg (fun h => hp (hpq.2 h))]; exact hy

/-- A loop over a list, each step of which gathers a list. -/
theorem GV.forInList (f : α → PUnit → W (ForInStep PUnit)) (g : α → List Aff)
    (hf : ∀ a, GV K (f a PUnit.unit) (ForInStep.yield PUnit.unit) (g a)) :
    ∀ xs : List α, GV K (forIn xs PUnit.unit f) PUnit.unit (xs.flatMap g)
  | [] => by
    rw [List.forIn_nil]
    exact GV.pure _
  | x :: xs => by
    rw [List.forIn_cons, List.flatMap_cons]
    exact GV.bind (hf x) (GV.forInList f g hf xs)

/-- Behind a routine that never returns nothing is said. -/
theorem GV.never_bind {r : W α} (h : ∀ acc, r K acc = none) (k : α → W β) (v : β) (l : List Aff) :
    GV K (r >>= k) v l := by
  refine GV.never (fun acc => ?_) v l
  simp only [Bind.bind, ReaderT.bind, StateT.bind, h acc]
  rfl

theorem GV.needSome (a : α) : GV K (W.need (some a)) a [] := GV.pure a

theorem GV.needNone (v : α) (l : List Aff) : GV K (W.need (none : Option α)) v l := GV.failure v l

/-- One form, then nothing more. -/
theorem GV.lin1 (f : Aff) {β : Type} (b : β) :
    GV K (W.lin f >>= fun _ => (Pure.pure b : W β)) b [f] :=
  GV.bind1 (GV.lin f) (GV.pure b)

end K5Law
