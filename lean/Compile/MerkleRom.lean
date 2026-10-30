-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/MerkleRom.lean: two readings of "the oracle algorithm x returns a", with their rules.
  `RunsIn tr x a` (Compile/Spec.lean)
                    a coin-free algorithm runs to the result a with all its queries and answers
                    taken from the trace tr. Here: what this says at `pure`, at a query and at one
                    single query (`runsIn_pure_iff`, `runsIn_query_iff`, `runsIn_ask_iff`); a
                    sequence of two algorithms runs within the trace exactly if both do
                    (`runsIn_bind_iff`); a larger trace does no harm (`RunsIn.mono`)
  `EvalsTo f x a`   under the oracle functions f the algorithm x returns a, whatever its coins
                    (`evalsTo_ask`: one single query returns f's value)
Both are closed under pure and bind (`Evaluates`, Compile/MerkleList.lean): `evaluates_runsIn`,
`evaluates_eager`.
-/
import Compile.MerkleList
import Rom.EagerLazy
import Compile.Spec

noncomputable section

namespace Compile
open Iop Rom Merkle

/-! ## `RunsIn` -/

section RunsIn

variable {S : OSpec} {α β : Type} {tr : Trace S}

theorem bind_eq (x : OComp S α) (f : α → OComp S β) : (x >>= f) = x.bind f := rfl

theorem pure_eq (a : α) : (pure a : OComp S α) = OComp.pure a := rfl

theorem runsIn_pure_iff {a b : α} : RunsIn tr (OComp.pure a : OComp S α) b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact RunsIn.pure a

theorem runsIn_query_iff {o : S.ι} {q : S.Dom o} {k : S.Rng o → OComp S α} {a : α} :
    RunsIn tr (OComp.query o q k) a ↔ ∃ r, (⟨o, q, r⟩ : QA S) ∈ tr ∧ RunsIn tr (k r) a := by
  constructor
  · intro h
    cases h with
    | query _ _ _ r _ hm hr => exact ⟨r, hm, hr⟩
  · rintro ⟨r, hm, hr⟩
    exact RunsIn.query o q k r a hm hr

theorem runsIn_ask_iff {o : S.ι} {q : S.Dom o} {r : S.Rng o} :
    RunsIn tr (OComp.ask o q) r ↔ (⟨o, q, r⟩ : QA S) ∈ tr := by
  rw [OComp.ask, runsIn_query_iff]
  constructor
  · rintro ⟨r', hm, hr⟩
    obtain rfl := runsIn_pure_iff.1 hr
    exact hm
  · intro hm
    exact ⟨r, hm, RunsIn.pure r⟩

/-- A sequence of two algorithms runs within the trace exactly if both do. -/
theorem runsIn_bind_iff (x : OComp S α) (f : α → OComp S β) (b : β) :
    RunsIn tr (x.bind f) b ↔ ∃ a, RunsIn tr x a ∧ RunsIn tr (f a) b := by
  induction x with
  | pure a =>
    simp only [OComp.bind]
    constructor
    · intro h; exact ⟨a, RunsIn.pure a, h⟩
    · rintro ⟨a', h1, h2⟩
      obtain rfl := runsIn_pure_iff.1 h1
      exact h2
  | query o q k ih =>
    simp only [OComp.bind, runsIn_query_iff, ih]
    constructor
    · rintro ⟨r, hm, a, h1, h2⟩; exact ⟨a, ⟨r, hm, h1⟩, h2⟩
    · rintro ⟨a, ⟨r, hm, h1⟩, h2⟩; exact ⟨r, hm, a, h1, h2⟩
  | sample n k _ =>
    simp only [OComp.bind]
    constructor
    · intro h; cases h
    · rintro ⟨a, h1, -⟩; cases h1

theorem RunsIn.mono {tr' : Trace S} (hs : tr ⊆ tr') {x : OComp S α} {a : α} (h : RunsIn tr x a) :
    RunsIn tr' x a := by
  induction h with
  | pure a => exact RunsIn.pure a
  | query o q k r a hm _ ih => exact RunsIn.query o q k r a (hs hm) ih

end RunsIn

variable {I X : Type} {lam : ℕ}

/-! ## `EvalsTo`, and both readings as `Evaluates` -/

section Eager

variable {S : OSpec}

/-- Under the oracle functions f the algorithm x returns a, whatever its coins. -/
def EvalsTo (f : Fam S) {α : Type} (x : OComp S α) (a : α) : Prop := x.runEager f = PMF.pure a

theorem evaluates_eager (f : Fam S) : Evaluates (OComp S) (fun {_} x a => EvalsTo f x a) where
  pure _ := rfl
  bind := by
    intro α β x g a b hx hg
    rw [EvalsTo] at hx hg ⊢
    rw [bind_eq, OComp.runEager_bind, hx, PMF.pure_bind, hg]

theorem evalsTo_ask (f : Fam S) (o : S.ι) (q : S.Dom o) : EvalsTo f (OComp.ask o q) (f o q) := rfl

theorem evaluates_runsIn (tr : Trace S) : Evaluates (OComp S) (fun {_} x a => RunsIn tr x a) where
  pure a := RunsIn.pure a
  bind := fun hx hg => (runsIn_bind_iff _ _ _).2 ⟨_, hx, hg⟩

end Eager

end Compile
