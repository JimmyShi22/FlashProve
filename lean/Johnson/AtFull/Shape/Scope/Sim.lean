-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/Sim.lean: TWO RUNS ON SHAPES THAT ARE RELATED STEP BY STEP RETURN ALIKE.
General in the two records of the type Shape (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean);
nothing is evaluated.

* run_rel: Rel n is a relation at the border in front of member n. Where at every member below N two
  shapes in Rel n are taken by the two steps to two shapes in Rel (n + 1), or both steps refuse, the
  two runs over N members from two shapes in Rel 0 do the same.
* yes_rel, yes_of_rel: so the named premise Shape.yes at the one is that at the other. yes_of_rel is
  the form at firstZA; its tests on values are free letters.
* yes_of_steps: equal steps below N give equal answers, whatever the tests on values: a run reads
  the steps alone.

Limits. Implications. No step is named, and nothing says that the premise on the steps holds at the
table of the first chain.
-/
import Johnson.AtFull.Shape.FrameForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open ProofFile.Honest (Shape)
open VerifiableInference.Desc.First (S)

/-- Both return, related, or both refuse. -/
def Alike {α β : Type} (Rel : α → β → Prop) (x : Except String α) (y : Except String β) : Prop :=
  (∃ b b', x = .ok b ∧ y = .ok b' ∧ Rel b b') ∨ (x.toOption = none ∧ y.toOption = none)

/-- Two runs that are related step by step are related. -/
theorem run_rel {σ σ' : Type} (Z : Shape σ) (Z' : Shape σ') (Rel : Nat → Z.Sh → Z'.Sh → Prop)
    {a : Z.Sh} {a' : Z'.Sh} (h : Rel 0 a a') : ∀ N : Nat,
    (∀ n, n < N → ∀ b b', Rel n b b' → Alike (Rel (n + 1)) (Z.g n b) (Z'.g n b')) →
    Alike (Rel N) (Z.run N a) (Z'.run N a')
  | 0, _ => Or.inl ⟨a, a', rfl, rfl, h⟩
  | N + 1, hs => by
    have ih := run_rel Z Z' Rel h N fun n hn => hs n (Nat.lt_succ_of_lt hn)
    have e1 : Z.run (N + 1) a = (Z.run N a).bind (Z.g N) := rfl
    have e2 : Z'.run (N + 1) a' = (Z'.run N a').bind (Z'.g N) := rfl
    rw [e1, e2]
    rcases ih with ⟨c, c', h1, h2, r⟩ | ⟨n1, n2⟩
    · rw [h1, h2]
      exact hs N (Nat.lt_succ_self N) c c' r
    · refine Or.inr ⟨?_, ?_⟩
      · cases h1 : Z.run N a with
        | error e => rfl
        | ok c =>
          rw [h1] at n1
          cases n1
      · cases h2 : Z'.run N a' with
        | error e => rfl
        | ok c =>
          rw [h2] at n2
          cases n2

/-- The named premise at the one run is that at the other. -/
theorem yes_rel {σ σ' : Type} (Z : Shape σ) (Z' : Shape σ') (Rel : Nat → Z.Sh → Z'.Sh → Prop)
    {a : Z.Sh} {a' : Z'.Sh} (h : Rel 0 a a') (N : Nat)
    (hs : ∀ n, n < N → ∀ b b', Rel n b b' → Alike (Rel (n + 1)) (Z.g n b) (Z'.g n b')) :
    Z.yes a N = Z'.yes a' N := by
  unfold Shape.yes
  rcases run_rel Z Z' Rel h N hs with ⟨c, c', h1, h2, -⟩ | ⟨n1, n2⟩
  · rw [h1, h2]
    rfl
  · rw [n1, n2]
    rfl

/-- **THE FORM AT firstZA.** The tests on values v, v' are free. -/
theorem yes_of_rel (Rel : Nat → ShA → ShA → Prop) {g g' : Nat → ShA → Except String ShA}
    {v v' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool} {N : Nat}
    (hs : ∀ n, n < N → ∀ a a', Rel n a a' → Alike (Rel (n + 1)) (g n a) (g' n a'))
    {a a' : ShA} (h : Rel 0 a a') : (firstZA g v).yes a N = (firstZA g' v').yes a' N :=
  yes_rel (firstZA g v) (firstZA g' v') Rel h N hs

/-- A run reads the steps alone: equal steps below N, whatever the tests on values. -/
theorem yes_of_steps {g g' : Nat → ShA → Except String ShA}
    {v v' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool} {N : Nat}
    (hs : ∀ n, n < N → g n = g' n) (a : ShA) : (firstZA g v).yes a N = (firstZA g' v').yes a N :=
  yes_of_rel (fun _ x y => x = y) (fun n hn b b' e => by
    subst e
    rw [hs n hn]
    cases h : g' n b with
    | ok c => exact Or.inl ⟨c, c, rfl, rfl, rfl⟩
    | error e => exact Or.inr ⟨rfl, rfl⟩) rfl

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.run_rel
#print axioms Johnson.AtFull.Shape.Scope.yes_rel
#print axioms Johnson.AtFull.Shape.Scope.yes_of_rel
#print axioms Johnson.AtFull.Shape.Scope.yes_of_steps
