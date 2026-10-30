-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Defs.lean: THE LAW OF THE COMPILED PROVER's OUTCOME: DEFINITIONS AND THE
STATEMENT. NO PROOF.

The compiled prover of one slot (proveX, OnBytes/Prover/Defs.lean) returns a string with the
transcript that was hashed, or the search of a round with a test has run out. Here is stated how
likely that is, and how its verifier messages are distributed, under oracles that are sampled lazily
from a table in which none of this chain's Fiat-Shamir queries has an entry.

Main names.
  GrApart, PutsApart   the numbers that a search may try are written apart: up to cap i in round i.
  FreshFrom   the table has no entry at a query to fb t that holds a plain part of the round whose
    number it holds, from round i on: BY PLACE, in the letters of RoundAt
    (Johnson/TypedOracleCompiler/RecCompile/SeedsApart.lean). A seed's two queries (rounds 1 and 2, a plain part of
    round 0) are no such queries: they may have entries.
  grFailAt, capFail   the sum over the rounds with a test of (1 - 2^-b)^(cap i + 1). They follow
    the earlier grFail, failOf and cFail (Compile/Batch/SpecGrind.lean) step for step.
  AccLaw   the form in which an accept law is spent: B is a set of verifier messages, a letter
    beside σ, x and y.
  Spec.prove_law   THE STATEMENT, as a Prop under a name: the idiom, and in part the form, of
    Spec.askW_law (Compile/Batch/SpecLoop.lean); proved in another file, spent under this name.

Limits. Definitions and one statement: nothing is proved here. Spec.prove_law names no goal of the
release. One slot, one chain. B's measure is taken with the test bits set to 0.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Prover.Main
import Johnson.TypedOracleCompiler.RecCompile.SeedsApart
import Rom.EagerLazy

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The numbers 0, .., cap are written apart. -/
def GrApart {C P : Type} (g : GrW C P) (cap : ℕ) : Prop :=
  ∀ (α : P) (n n' : ℕ), n ≤ cap → n' ≤ cap → g.put n α = g.put n' α → n = n'

/-- In every round with a test the numbers that the search may try are written apart. i: the number
of the first of the rounds s. -/
def PutsApart : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → Prop
  | [], _, _, _, _ => True
  | _ :: s, (a, A), (w, W), cap, i =>
      (match a.kind with
        | .lo => ∀ g, w.grJ = some g → GrApart g (cap i)
        | .sh => ∀ g, w.gr0 = some g → GrApart g (cap i)) ∧ PutsApart s A W cap (i + 1)

/-- The table has no entry at a query to fb t that holds a plain part of one of the rounds s and the
number of that round. i: the number of the first of the rounds s. -/
def FreshFrom (t : Tag) (s : Shape) (A : RoundSplits s) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (T : Table (typedOracleFamily lam K L)) : Prop :=
  ∀ q : FbIn lam L t, (∃ z, q.plain = embP z ∧ q.round = i + PlainPart.depth s A z) →
    T (OracleName.fb t) q = none

/-- (1 - 2^-b)^(n + 1): no one of n + 1 tries passes. -/
def grFailAt {C P : Type} (n : ℕ) : Option (GrW C P) → ℝ≥0∞
  | none => 0
  | some g => (1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹) ^ (n + 1)

/-- The sum over the rounds of the probability that the round's search fails. -/
def capFail : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → ℝ≥0∞
  | [], _, _, _, _ => 0
  | _ :: s, (a, A), (w, W), cap, i =>
      (match a.kind with
        | .lo => grFailAt (cap i) w.grJ
        | .sh => grFailAt (cap i) w.gr0) + capFail s A W cap (i + 1)

/-- The form in which an accept law is spent: at every transcript that is the strategy's own run but
for nonces, with all tests passed, and whose verifier messages lie outside B, the interactive
verifier accepts. -/
def AccLaw {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y) (y : E.Str)
    (σ : Strat Q.loc.shape Unit) (B : Set (Rho Q.loc.shape)) : Prop :=
  ∀ τ : Tr Q.loc.shape, RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh τ.rho = true →
    Puts Q.loc.shape Q.ann wq.sh (σ.run τ.rho).1 τ → τ.rho ∉ B → Q.loc.accept x y τ = true

/-- **THE STATEMENT.** From any table that is fresh for this chain: the prover's search runs out, or
it draws verifier messages in B, with probability at most (the searches' failure) + (the uniform
measure of B, the test bits set to 0). -/
def Spec.prove_law : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ) (T : Table (typedOracleFamily lam K L)),
    FreshFrom t Q.loc.shape Q.ann embP 0 T → wq.OKG → Q.ann.Fmt →
    PutsApart Q.loc.shape Q.ann wq.sh cap 0 → Function.Injective embP →
    ∀ B : Set (Rho Q.loc.shape),
      PrFrom T (proveX t Q wq embS embP xin cms x y xt σ co cap)
          {r | (∃ j, r = .ranOut j) ∨ ∃ π τ, r = .ok (π, τ) ∧ τ.rho ∈ B} ≤
        capFail Q.loc.shape Q.ann wq.sh cap 0 +
          pr (unif (Rho Q.loc.shape)) {ρ | RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ B}

end OnBytes.Prover
