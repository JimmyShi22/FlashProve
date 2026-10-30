-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecDerive.lean: the committer's coins derived from one seed through a random oracle, as a
transformation of any commit-and-prove argument. Definitions only. Lemmas: Rom/Derive.lean. The
theorem: Rom/DeriveWith.lean (`deriveWith`).

The transformation. The family S of oracles has an auxiliary oracle `σ.o`, which the scheme A never
queries (`ArgAvoids`). So the hypothesis on A is already about adversaries who query that oracle,
and about a simulator that answers it. The derived scheme is over the same family:
    C' i          samples a seed s, runs C i with its j-th uniform sample replaced by ψ (answer of
                  σ.o at the query (s, j)), and keeps (i, s) in place of isk;
    P' (i, s) b   runs C i again in the same way, which gives the same isk, and then P isk b (with
                  fresh coins, as before);
    V'            is V.
A uniform sample is from Fin (n + 1), and ψ n maps an answer of the auxiliary oracle to Fin (n + 1);
`σ.bias n` is the distance of ψ n (uniform) from uniform, and `OComp.pathBias` is the supremum, over
the paths of an algorithm, of the sum of these distances along the path. A second derived run, on
any table and record that contain those which the first run returns, returns the same result
(`runRec_again`, Rom/Derive.lean, where its label is (Use)); (Use) holds because C' and P' run the
same program.

The theorem (`deriveWith` and `replays_derived`, Rom/DeriveWith.lean; for `derived` no declaration
states it; see `derivedWith_derived`). If A has the bounds (α, ε, ζ), then with the same extractor
and the same simulator: completeness error α + b; index binding unchanged (it is about V only);
index privacy ζ(t, N) + t / (number of seeds) + b, where b bounds the path bias of C i for all i. P'
is slow: it repeats the whole of C. A prover that derives only what a session needs is
scheme-specific: Rom/DeriveWith.lean has the theorem for every prover that replays the key.

Notation:
  `Gen.Arg` (ZKCP/Gen.lean): ARG = (C, P, V) over the family S; `C : I → OComp S (IVK × ISK)`: at an
      index i it returns ivk and isk; P takes isk and a batch, V takes ivk and one pair (x, π)
  index binding, index privacy: `HasIndexBindingWith`, `HasIndexPrivacyWith` (ZKCP/Gen.lean)
  b: in the row of P' a batch, of type `List (X × W)`; under "The theorem" a number, of type `ℝ≥0∞`
-/
import ZKCP.Gen
import Prob.Tv
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob

namespace Rom

variable {S : OSpec} {α : Type}

/-- An auxiliary oracle, used as a source of coins: seeds are the elements of Fin (sd + 1); pt s j
is the query for the seed s and the counter j, and different pairs have different queries; ψ n turns
an answer into a sample with n + 1 outcomes. -/
structure SeedOracle (S : OSpec) where
  o : S.ι
  sd : ℕ
  pt : Fin (sd + 1) → ℕ → S.Dom o
  inj : ∀ s j s' j', pt s j = pt s' j' → s = s' ∧ j = j'
  ψ : (n : ℕ) → S.Rng o → Fin (n + 1)

/-- the distance of a derived sample from a uniform one -/
def SeedOracle.bias (σ : SeedOracle S) (n : ℕ) : ℝ≥0∞ :=
  tv ((PMF.uniformOfFintype (S.Rng σ.o)).map (σ.ψ n)) (PMF.uniformOfFintype (Fin (n + 1)))

namespace OComp

/-- the algorithm never queries the oracle o -/
def Avoids (o : S.ι) : OComp S α → Prop
  | pure _ => True
  | query o' _ k => o' ≠ o ∧ ∀ r, (k r).Avoids o
  | sample _ k => ∀ r, (k r).Avoids o

/-- The algorithm with its coins derived under the seed s; j is the number of samples so far. -/
def derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) : OComp S α → ℕ → OComp S α
  | pure a, _ => pure a
  | query o q k, j => query o q fun r => (k r).derive σ s j
  | sample n k, j => query σ.o (σ.pt s j) fun d => (k (σ.ψ n d)).derive σ s (j + 1)

/-- the supremum, over the paths of the algorithm, of the sum along the path of the distances of the
derived samples from uniform ones -/
def pathBias (σ : SeedOracle S) : OComp S α → ℝ≥0∞
  | pure _ => 0
  | query _ _ k => ⨆ r, (k r).pathBias σ
  | sample n k => σ.bias n + ⨆ r, (k r).pathBias σ

end OComp

open ZKCP

variable {I X W PP IVK ISK Pf : Type}

/-- none of the three algorithms ever queries the oracle o -/
structure ArgAvoids (A : Gen.Arg S I X W IVK ISK Pf) (o : S.ι) : Prop where
  C : ∀ i, (A.C i).Avoids o
  P : ∀ isk b, (A.P isk b).Avoids o
  V : ∀ ivk x π, (A.V ivk x π).Avoids o

/-- The derived scheme. Only the coins of C are derived. The coins of P itself stay fresh in every
call, so P' is stateless as P is, and its calls are independent given the key. -/
def derived (A : Gen.Arg S I X W IVK ISK Pf) (σ : SeedOracle S) :
    Gen.Arg S I X W IVK (I × Fin (σ.sd + 1)) Pf where
  C := fun i =>
    OComp.sample σ.sd fun s => ((A.C i).derive σ s 0).bind fun out => OComp.pure (out.1, (i, s))
  P := fun k b => ((A.C k.1).derive σ k.2 0).bind fun out => A.P out.2 b
  V := A.V

end Rom
