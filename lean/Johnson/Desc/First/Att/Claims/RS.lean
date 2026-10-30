-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/RS.lean: kind K5, the claims: the rules for "two routines return
together". The routines of Johnson/Desc/First/Att/RunsP.lean live in W α := ReaderT Nat (StateT
(Array Aff) Option) α.

Main names:
  `RS K R r r'`: at K, from whatever was gathered on either side, r and r' either both refuse or
    both return, and then their values stand in the relation R.
  The rules: pure, bind, fail, mono, ite, read, lin, mustAs, need, foldlM₂ and foldlM1 (two lists
    member by member; one list), forM₂ and forM1, forIn1.
They serve Johnson/Desc/First/Att/Claims/Same.lean and Johnson/Desc/First/Att/Claims/Returns.lean:
whether a run of the claims returns depends on public numbers and lengths alone.
Nothing of OnBytes is used but the type of a form.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.GV

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P.Runs (W)
open VerifiableInference.Desc.First.Att

variable {α α' β β' σ σ' : Type} {K : ℕ}

/-- Both refuse, or both return and the values are related. -/
def ORel (R : α → α' → Prop) : Option (α × Array Aff) → Option (α' × Array Aff) → Prop
  | some x, some x' => R x.1 x'.1
  | none, none => True
  | _, _ => False

/-- At K, from whatever was gathered: both refuse, or both return related values. -/
def RS (K : ℕ) (R : α → α' → Prop) (r : W α) (r' : W α') : Prop :=
  ∀ acc acc', ORel R (r K acc) (r' K acc')

/-- The relation that holds always. -/
def Any (_ : α) (_ : α') : Prop := True

theorem bind_none {r : W α} {k : α → W β} {acc : Array Aff} (h : r K acc = none) :
    (r >>= k) K acc = none := by
  simp only [Bind.bind, ReaderT.bind, StateT.bind, h]
  rfl

theorem bind_some {r : W α} {k : α → W β} {acc : Array Aff} {x : α × Array Aff}
    (h : r K acc = some x) : (r >>= k) K acc = k x.1 K x.2 := by
  simp only [Bind.bind, ReaderT.bind, StateT.bind, h]
  rfl

theorem RS.pure {R : α → α' → Prop} {a : α} {a' : α'} (h : R a a') :
    RS K R (Pure.pure a : W α) (Pure.pure a' : W α') := fun _ _ => h

theorem RS.fail {R : α → α' → Prop} : RS K R (failure : W α) (failure : W α') := fun _ _ => trivial

theorem RS.bind {R : α → α' → Prop} {Q : β → β' → Prop} {r : W α} {r' : W α'} {k : α → W β}
    {k' : α' → W β'} (h1 : RS K R r r') (h2 : ∀ a a', R a a' → RS K Q (k a) (k' a')) :
    RS K Q (r >>= k) (r' >>= k') := by
  intro acc acc'
  have h := h1 acc acc'
  cases hr : r K acc with
  | none =>
    cases hr' : r' K acc' with
    | none => rw [bind_none hr, bind_none hr']; trivial
    | some x' => rw [hr, hr'] at h; exact h.elim
  | some x =>
    cases hr' : r' K acc' with
    | none => rw [hr, hr'] at h; exact h.elim
    | some x' =>
      rw [hr, hr'] at h
      rw [bind_some hr, bind_some hr']
      exact h2 _ _ h _ _

theorem RS.mono {R Q : α → α' → Prop} {r : W α} {r' : W α'} (h : RS K R r r')
    (hRQ : ∀ a a', R a a' → Q a a') : RS K Q r r' := by
  intro acc acc'
  have h := h acc acc'
  cases hr : r K acc <;> cases hr' : r' K acc' <;> rw [hr, hr'] at h
  · trivial
  · exact h.elim
  · exact h.elim
  · exact hRQ _ _ h

theorem RS.ite {R : α → α' → Prop} {p q : Prop} [Decidable p] [Decidable q] (hpq : p ↔ q)
    {x y : W α} {x' y' : W α'} (hx : RS K R x x') (hy : RS K R y y') :
    RS K R (if p then x else y) (if q then x' else y') := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (hpq.1 hp)]; exact hx
  · rw [if_neg hp, if_neg (fun h => hp (hpq.2 h))]; exact hy

theorem RS.read : RS K Eq (read : W ℕ) (read : W ℕ) := fun _ _ => rfl

theorem RS.lin (f f' : Aff) : RS K Any (W.lin f) (W.lin f') := fun _ _ => trivial

theorem RS.mustAs (n n' : String) {b b' : Bool} (h : b = b') :
    RS K Any (P.Runs.mustAs n b) (P.Runs.mustAs n' b') := by
  subst h
  unfold P.Runs.mustAs
  split
  · exact RS.pure trivial
  · exact RS.fail

theorem RS.refuse {R : α → α' → Prop} (n n' : String) :
    RS K R (P.Runs.refuse n : W α) (P.Runs.refuse n' : W α') := RS.fail

/-- Two options: both none, or both some and related. -/
def OptRel (R : α → α' → Prop) : Option α → Option α' → Prop
  | some a, some a' => R a a'
  | none, none => True
  | _, _ => False

theorem RS.need {R : α → α' → Prop} {x : Option α} {x' : Option α'} (h : OptRel R x x') :
    RS K R (W.need x) (W.need x') := by
  cases x <;> cases x'
  · exact RS.fail
  · exact h.elim
  · exact h.elim
  · exact RS.pure h

theorem RS.foldlM₂ {P : α → α' → Prop} {R : σ → σ' → Prop} {f : σ → α → W σ} {f' : σ' → α' → W σ'}
    (hf : ∀ s s' a a', R s s' → P a a' → RS K R (f s a) (f' s' a')) :
    ∀ {xs : List α} {xs' : List α'}, List.Forall₂ P xs xs' → ∀ {s : σ} {s' : σ'}, R s s' →
      RS K R (xs.foldlM f s) (xs'.foldlM f' s')
  | _, _, .nil, _, _, hs => by
    simp only [List.foldlM_nil]
    exact RS.pure hs
  | _, _, .cons ha hl, _, _, hs => by
    simp only [List.foldlM_cons]
    exact RS.bind (hf _ _ _ _ hs ha) fun _ _ h => RS.foldlM₂ hf hl h

theorem forall₂_same {P : α → α → Prop} (h : ∀ a, P a a) : ∀ xs : List α, List.Forall₂ P xs xs
  | [] => .nil
  | a :: xs => .cons (h a) (forall₂_same h xs)

theorem RS.foldlM1 {R : σ → σ' → Prop} {f : σ → α → W σ} {f' : σ' → α → W σ'}
    (hf : ∀ s s' a, R s s' → RS K R (f s a) (f' s' a)) (xs : List α) {s : σ} {s' : σ'}
    (hs : R s s') : RS K R (xs.foldlM f s) (xs.foldlM f' s') :=
  RS.foldlM₂ (P := Eq) (fun s s' a _ h e => e ▸ hf s s' a h) (forall₂_same (fun _ => rfl) xs) hs

theorem RS.forM₂ {P : α → α' → Prop} {f : α → W PUnit} {f' : α' → W PUnit}
    (hf : ∀ a a', P a a' → RS K Any (f a) (f' a')) :
    ∀ {xs : List α} {xs' : List α'}, List.Forall₂ P xs xs' → RS K Any (xs.forM f) (xs'.forM f')
  | _, _, .nil => RS.pure trivial
  | _, _, .cons ha hl => RS.bind (hf _ _ ha) fun _ _ _ => RS.forM₂ hf hl

theorem RS.forM1 {f f' : α → W PUnit} (hf : ∀ a, RS K Any (f a) (f' a)) (xs : List α) :
    RS K Any (xs.forM f) (xs.forM f') :=
  RS.forM₂ (P := Eq) (fun a _ e => e ▸ hf a) (forall₂_same (fun _ => rfl) xs)

/-- Both steps go on. -/
def Yield (x x' : ForInStep PUnit) : Prop := x = ForInStep.yield PUnit.unit ∧ x' = ForInStep.yield PUnit.unit

theorem RS.forIn1 {f f' : α → PUnit → W (ForInStep PUnit)}
    (hf : ∀ a, RS K Yield (f a PUnit.unit) (f' a PUnit.unit)) :
    ∀ xs : List α, RS K Any (forIn xs PUnit.unit f) (forIn xs PUnit.unit f')
  | [] => by
    rw [List.forIn_nil, List.forIn_nil]
    exact RS.pure trivial
  | x :: xs => by
    rw [List.forIn_cons, List.forIn_cons]
    refine RS.bind (hf x) fun a a' h => ?_
    obtain ⟨rfl, rfl⟩ := h
    exact RS.forIn1 hf xs

theorem RS.yield : RS K Yield (Pure.pure (ForInStep.yield PUnit.unit) : W (ForInStep PUnit))
    (Pure.pure (ForInStep.yield PUnit.unit)) := RS.pure ⟨rfl, rfl⟩

/-- A step that ends in one form. -/
theorem RS.linYield (f f' : Aff) :
    RS K Yield (W.lin f >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _))
      (W.lin f' >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _)) :=
  RS.bind (RS.lin f f') fun _ _ _ => RS.yield

end K5Law
