-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsKit.lean: A RELATIONAL KIT FOR THE ROUTINES THAT GATHER AN ATTENTION
SEGMENT's CLAIMS (W, Johnson/Desc/First/Att/RunsP.lean): TWO ROUTINES REFUSE TOGETHER, OR RETURN
RELATED VALUES AND GATHER FORMS OF ONE SHAPE. After the library's kit for returns (RS,
Johnson/Desc/First/Att/Claims/RS.lean), rule for rule, with one relation more. Definitions, and
general rules with their proofs: of the kind's text the four verbs `lin`, `mustAs`, `refuse`, `need`
alone are named; no routine that gathers claims.

Why. The library's `RS` says of two routines that they return at both or at neither, and forgets the
forms that they gather. A run of claims owes on shapes the shapes of its claims (AffSh,
Johnson/Desc/First/Shape/Parts.lean).

Main names:
  `formsSh`, `formsSh_push`   the shapes of what has been gathered
  `SameF`   two forms have one shape
  `OShape`, `RSh`   both refuse, or both return related values, and what is gathered has one shape,
    from gathered arrays of one shape
  `RSh.pure`, `fail`, `bind`, `mono`, `ite`, `read`, `lin`, `mustAs`, `refuse`, `need`, `foldlM₂`,
    `foldlM1`, `forM₂`, `forM1`, `forIn1`, `yield`, `linYield`   the rules
  `RSh.returns`   at one gathered array on both sides the library's relation on returns (`ORel`)
    follows; not its `RS`, which speaks of any two arrays

Limits. General rules. Nothing is said of any routine of the kind.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.RS
import Johnson.Desc.First.Shape.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (W)
open VerifiableInference.Desc.First.Shape (AffSh affSh)
open K5Law (bind_none bind_some Any OptRel forall₂_same Yield RS ORel)

variable {α α' β β' σ σ' : Type} {K : ℕ}

/-- The shapes of the forms that have been gathered, in order. -/
def formsSh (acc : Array Aff) : List AffSh := acc.toList.map affSh

theorem formsSh_push (acc : Array Aff) (f : Aff) :
    formsSh (acc.push f) = formsSh acc ++ [affSh f] := by
  unfold formsSh
  rw [Array.toList_push, List.map_append]
  rfl

/-- Two forms have one shape. -/
def SameF (f f' : Aff) : Prop := affSh f = affSh f'

/-- Both refuse, or both return, the values are related, and what is gathered has one shape. -/
def OShape (R : α → α' → Prop) : Option (α × Array Aff) → Option (α' × Array Aff) → Prop
  | some x, some x' => R x.1 x'.1 ∧ formsSh x.2 = formsSh x'.2
  | none, none => True
  | _, _ => False

/-- At K, from gathered arrays of one shape: both refuse, or both return related values and arrays
of one shape. -/
def RSh (K : ℕ) (R : α → α' → Prop) (r : W α) (r' : W α') : Prop :=
  ∀ acc acc', formsSh acc = formsSh acc' → OShape R (r K acc) (r' K acc')

theorem RSh.pure {R : α → α' → Prop} {a : α} {a' : α'} (h : R a a') :
    RSh K R (Pure.pure a : W α) (Pure.pure a' : W α') := fun _ _ e => ⟨h, e⟩

theorem RSh.fail {R : α → α' → Prop} : RSh K R (failure : W α) (failure : W α') :=
  fun _ _ _ => trivial

theorem RSh.bind {R : α → α' → Prop} {Q : β → β' → Prop} {r : W α} {r' : W α'} {k : α → W β}
    {k' : α' → W β'} (h1 : RSh K R r r') (h2 : ∀ a a', R a a' → RSh K Q (k a) (k' a')) :
    RSh K Q (r >>= k) (r' >>= k') := by
  intro acc acc' e
  have h := h1 acc acc' e
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
      exact h2 _ _ h.1 _ _ h.2

theorem RSh.mono {R Q : α → α' → Prop} {r : W α} {r' : W α'} (h : RSh K R r r')
    (hRQ : ∀ a a', R a a' → Q a a') : RSh K Q r r' := by
  intro acc acc' e
  have h := h acc acc' e
  cases hr : r K acc <;> cases hr' : r' K acc' <;> rw [hr, hr'] at h
  · trivial
  · exact h.elim
  · exact h.elim
  · exact ⟨hRQ _ _ h.1, h.2⟩

theorem RSh.ite {R : α → α' → Prop} {p q : Prop} [Decidable p] [Decidable q] (hpq : p ↔ q)
    {x y : W α} {x' y' : W α'} (hx : RSh K R x x') (hy : RSh K R y y') :
    RSh K R (if p then x else y) (if q then x' else y') := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (hpq.1 hp)]; exact hx
  · rw [if_neg hp, if_neg (fun h => hp (hpq.2 h))]; exact hy

theorem RSh.read : RSh K Eq (read : W ℕ) (read : W ℕ) := fun _ _ e => ⟨rfl, e⟩

/-- One form more, of one shape. -/
theorem RSh.lin {f f' : Aff} (h : SameF f f') : RSh K Any (W.lin f) (W.lin f') :=
  fun acc acc' e => by
    have h' : affSh f = affSh f' := h
    show Any _ _ ∧ formsSh (acc.push f) = formsSh (acc'.push f')
    exact ⟨trivial, by rw [formsSh_push, formsSh_push, e, h']⟩

theorem RSh.mustAs (n n' : String) {b b' : Bool} (h : b = b') :
    RSh K Any (P.Runs.mustAs n b) (P.Runs.mustAs n' b') := by
  subst h
  unfold P.Runs.mustAs
  split
  · exact RSh.pure trivial
  · exact RSh.fail

theorem RSh.refuse {R : α → α' → Prop} (n n' : String) :
    RSh K R (P.Runs.refuse n : W α) (P.Runs.refuse n' : W α') := RSh.fail

theorem RSh.need {R : α → α' → Prop} {x : Option α} {x' : Option α'} (h : OptRel R x x') :
    RSh K R (W.need x) (W.need x') := by
  cases x <;> cases x'
  · exact RSh.fail
  · exact h.elim
  · exact h.elim
  · exact RSh.pure h

theorem RSh.foldlM₂ {P : α → α' → Prop} {R : σ → σ' → Prop} {f : σ → α → W σ}
    {f' : σ' → α' → W σ'} (hf : ∀ s s' a a', R s s' → P a a' → RSh K R (f s a) (f' s' a')) :
    ∀ {xs : List α} {xs' : List α'}, List.Forall₂ P xs xs' → ∀ {s : σ} {s' : σ'}, R s s' →
      RSh K R (xs.foldlM f s) (xs'.foldlM f' s')
  | _, _, .nil, _, _, hs => by
    simp only [List.foldlM_nil]
    exact RSh.pure hs
  | _, _, .cons ha hl, _, _, hs => by
    simp only [List.foldlM_cons]
    exact RSh.bind (hf _ _ _ _ hs ha) fun _ _ h => RSh.foldlM₂ hf hl h

theorem RSh.foldlM1 {R : σ → σ' → Prop} {f : σ → α → W σ} {f' : σ' → α → W σ'}
    (hf : ∀ s s' a, R s s' → RSh K R (f s a) (f' s' a)) (xs : List α) {s : σ} {s' : σ'}
    (hs : R s s') : RSh K R (xs.foldlM f s) (xs.foldlM f' s') :=
  RSh.foldlM₂ (P := Eq) (fun s s' a _ h e => e ▸ hf s s' a h) (forall₂_same (fun _ => rfl) xs) hs

theorem RSh.forM₂ {P : α → α' → Prop} {f : α → W PUnit} {f' : α' → W PUnit}
    (hf : ∀ a a', P a a' → RSh K Any (f a) (f' a')) :
    ∀ {xs : List α} {xs' : List α'}, List.Forall₂ P xs xs' → RSh K Any (xs.forM f) (xs'.forM f')
  | _, _, .nil => RSh.pure trivial
  | _, _, .cons ha hl => RSh.bind (hf _ _ ha) fun _ _ _ => RSh.forM₂ hf hl

theorem RSh.forM1 {f f' : α → W PUnit} (hf : ∀ a, RSh K Any (f a) (f' a)) (xs : List α) :
    RSh K Any (xs.forM f) (xs.forM f') :=
  RSh.forM₂ (P := Eq) (fun a _ e => e ▸ hf a) (forall₂_same (fun _ => rfl) xs)

theorem RSh.forIn1 {f f' : α → PUnit → W (ForInStep PUnit)}
    (hf : ∀ a, RSh K Yield (f a PUnit.unit) (f' a PUnit.unit)) :
    ∀ xs : List α, RSh K Any (forIn xs PUnit.unit f) (forIn xs PUnit.unit f')
  | [] => by
    rw [List.forIn_nil, List.forIn_nil]
    exact RSh.pure trivial
  | x :: xs => by
    rw [List.forIn_cons, List.forIn_cons]
    refine RSh.bind (hf x) fun a a' h => ?_
    obtain ⟨rfl, rfl⟩ := h
    exact RSh.forIn1 hf xs

theorem RSh.yield : RSh K Yield (Pure.pure (ForInStep.yield PUnit.unit) : W (ForInStep PUnit))
    (Pure.pure (ForInStep.yield PUnit.unit)) := RSh.pure ⟨rfl, rfl⟩

/-- A step that ends in one form. -/
theorem RSh.linYield {f f' : Aff} (h : SameF f f') :
    RSh K Yield (W.lin f >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _))
      (W.lin f' >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _)) :=
  RSh.bind (RSh.lin h) fun _ _ _ => RSh.yield

/-- At one gathered array the library's relation on returns follows. -/
theorem RSh.returns {R : α → α' → Prop} {r : W α} {r' : W α'} (h : RSh K R r r')
    (acc : Array Aff) : ORel R (r K acc) (r' K acc) := by
  have k := h acc acc rfl
  cases hr : r K acc <;> cases hr' : r' K acc <;> rw [hr, hr'] at k
  · trivial
  · exact k.elim
  · exact k.elim
  · exact k.1

end H2K5.Honest

#print axioms H2K5.Honest.formsSh_push
#print axioms H2K5.Honest.RSh.pure
#print axioms H2K5.Honest.RSh.fail
#print axioms H2K5.Honest.RSh.bind
#print axioms H2K5.Honest.RSh.mono
#print axioms H2K5.Honest.RSh.ite
#print axioms H2K5.Honest.RSh.read
#print axioms H2K5.Honest.RSh.lin
#print axioms H2K5.Honest.RSh.mustAs
#print axioms H2K5.Honest.RSh.refuse
#print axioms H2K5.Honest.RSh.need
#print axioms H2K5.Honest.RSh.foldlM₂
#print axioms H2K5.Honest.RSh.foldlM1
#print axioms H2K5.Honest.RSh.forM₂
#print axioms H2K5.Honest.RSh.forM1
#print axioms H2K5.Honest.RSh.forIn1
#print axioms H2K5.Honest.RSh.yield
#print axioms H2K5.Honest.RSh.linYield
#print axioms H2K5.Honest.RSh.returns
