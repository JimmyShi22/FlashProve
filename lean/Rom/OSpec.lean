-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/OSpec.lean: a family of independent random oracles.
  Imports Mathlib only.

  Credit. The public Lean library VCV-io (https://github.com/Verified-zkEVM/VCV-io) also represents
  an algorithm with oracle access as a tree of queries.
  This file holds what such a tree asks: a family of oracles, given by names, domains and finite
  ranges; the trees are in Rom/OComp.lean.
  VCV-io is not a dependency:
  no file of this library imports it.
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
noncomputable section -- Lean tags what it cannot compile

namespace Rom

/-- A family of oracles: names, and for each name a domain and a finite, non-empty range.
Each oracle is a uniformly random function Dom o → Rng o, and all are independent (`U`,
Rom/Measure.lean; `OComp.runLazy`, Rom/OComp.lean). -/
structure OSpec where
  ι : Type
  Dom : ι → Type
  Rng : ι → Type
  [decι : DecidableEq ι]
  [finRng : ∀ o, Fintype (Rng o)]
  [neRng : ∀ o, Nonempty (Rng o)]

attribute [instance] OSpec.decι OSpec.finRng OSpec.neRng

/-- Equality of queries is decided classically. This is no part of a family of oracles: it enters
the semantics (tables of lazy sampling, events about traces). -/
instance OSpec.decDom (S : OSpec) (o : S.ι) : DecidableEq (S.Dom o) :=
  Classical.decEq _

/-- The model of ZKCP/Defs.lean: one oracle {0,1}* → {0,1}^lam. -/
def rom (lam : ℕ) : OSpec where
  ι := Unit
  Dom := fun _ => List Bool
  Rng := fun _ => Fin lam → Bool

/-- One query with its answer. -/
abbrev QA (S : OSpec) : Type := Σ o : S.ι, S.Dom o × S.Rng o
/-- A query-answer trace, first query first. -/
abbrev Trace (S : OSpec) : Type := List (QA S)

/-- A whole family of functions. -/
abbrev Fam (S : OSpec) : Type := ∀ o : S.ι, S.Dom o → S.Rng o

/-- A partial table: what lazy sampling has fixed so far. -/
abbrev Table (S : OSpec) : Type := ∀ o : S.ι, S.Dom o → Option (S.Rng o)

def Table.empty (S : OSpec) : Table S := fun _ _ => none

/-- Write (or overwrite) one entry. -/
def Table.set {S : OSpec} (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    Table S :=
  Function.update T o (Function.update (T o) q (some r))

end Rom
