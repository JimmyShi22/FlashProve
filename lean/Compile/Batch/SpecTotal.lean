-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecTotal.lean: two terms of the hash part of ζ for the compiled scheme, where the
adversary has one bound of t queries in all (the lemma on deferred programming for a total query
bound: Rom/SpecDeferTotal.lean). Definitions only, for a wire record W, parameters p and n batches;
the counts `xTree`, `xFb`, `xReq` are those of Compile/Batch/Counts.lean. (Words of this library:
lean/GLOSSARY.md.)

  `muB`   meant as a bound on the probability that one query of the adversary hits a marked query,
          whichever oracle it goes to. Each query goes to one oracle, so there is a maximum over the
          oracles where a query bound for each oracle would give a sum
  `hashSqB`   the part that does not depend on t: xTree² / 2^sMT + xTree² / 2^λ + xFb² / 2^min(sFS,
              λ) + 3 xReq² / 2^λ

Who uses them. The bound of the scheme whose rounds may have proof-of-work bits:
Compile/Batch/SpecTotalG.lean (zetaHashBGTot = the overrun term + t * muB + hashSqBG; `zetaBGTot`),
Compile/Batch/TotalG.lean (`hashSqB` in a proof).

Limits. No statement is here, and none on a probability: what is stated of `muB` is that the
maximum, over the oracles and the ghost names `fbw t k` (Compile/Batch/Oracles.lean), of (marked
queries) / 2^(bits of the charged token) is at most `muB` (Compile/Batch/SpecTotalG.lean:
`Spec.supBG`; proved: Compile/Batch/TotalG.lean: `supBG`). The counts are upper bounds (ordinary and
marked queries together for the trees; one count for the three Fiat-Shamir oracles). Nothing at
concrete parameters.
-/
import Compile.Batch.Spec
import Compile.Batch.SpecDiscipline
import Compile.Batch.Chall
import Rom.SpecDeferTotal

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.GlueB (GCall SCall GAdm asW realW Close)
open Compile.BatchLife (LifeOutB LifeInB LifeB LifeAdmB)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- Meant as a bound on the probability that one query of the adversary hits a marked query,
whichever oracle it goes to. (The counts are upper bounds: ordinary and marked queries together for
the trees, one count for the three Fiat-Shamir oracles.) -/
def muB (W : QueryLayout lam L) (p : Params) (n : ℕ) : ℝ≥0∞ :=
  max ((xTree W p n : ℝ≥0∞) / 2 ^ p.sMT)
    (max ((xTree W p n : ℝ≥0∞) / 2 ^ lam)
      (max ((xFb (L := L) p n : ℝ≥0∞) / 2 ^ (min p.sFS lam)) ((xReq L n : ℝ≥0∞) / 2 ^ lam)))

/-- the four hash terms that do not depend on the adversary's number t of queries (those of
zetaHashB, which is not in this library, at t = 0) -/
def hashSqB (W : QueryLayout lam L) (p : Params) (n : ℕ) : ℝ≥0∞ :=
  (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ p.sMT
    + (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ lam
    + (xFb (L := L) p n : ℝ≥0∞) * (0 + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam)
    + 3 * ((xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam)






end Compile.Batch
