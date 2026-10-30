-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecTotalG.lean: the hash term of the compiled scheme with proof-of-work bits, for one
query bound of the adversary. Terms of the bound and statements. The proofs:
Compile/Batch/TotalG.lean. (Words of this library: lean/GLOSSARY.md.)

The statements here are on counts. This file does not state index privacy of any scheme. The term
`zetaBGTot` enters the privacy bound of the schemes with proof-of-work bits that have the entries in
the key and no query for an empty slot, from the form that is generic in the bound of the game hop;
exactly: that of `Gen.withW Wn (argBKE W WP p)`, under the hypotheses of `Spec.compileWireT_any`,
CompileK/WideMain.lean, where it is written `zetaBGen L p M (hashTermsBGTot W p)`
(`zetaBGTot_eq_gen`, Compile/Batch/HopTot.lean). For the schemes with a seed, the lazy prover and
pruned Merkle paths this is neither stated nor proved in this library; the steps to them are
implications (Compile/Batch/StepSGr.lean, Compile/Batch/StepL.lean, Compile/Batch/StarO.lean).

Where the factor more + 1 of a bound with a budget for each oracle comes from
(Compile/Batch/SpecGrind.lean, Bounds). In a round with proof-of-work bits the honest prover makes
its Fiat-Shamir query up to more + 1 times (a search), with inputs that hold the same secret string.
The token programs make attempt number k + 1 under a ghost name, `fbw t k`
(Compile/Batch/SpecGhost.lean), so that the string is charged at most once at each oracle. The lemma
on deferred programming in its first form (`Rom.Spec.defer`) has a query bound (a budget) for each
oracle, and an adversary that has been translated back along the exchange of queries keeps its total
query bound t only. So a bound from that form counts t at every oracle: xFbG (t + xFbG) / 2^min(sFS,
λ), xFbG = all attempts.

The term here, from the lemma on deferred programming for a total query bound
(Rom/SpecDeferTotal.lean):
* The part that is linear in t is that of the scheme without proof-of-work bits: t * muB W p n
  (Compile/Batch/SpecTotal.lean). The reason (`Spec.supBG`): no Fiat-Shamir oracle `fb t` and no
  ghost name `fbw t k` has more marked queries than there are Fiat-Shamir queries without
  proof-of-work bits (xFb), and all of these are charged to tokens of the same least length. The
  number of attempts does not occur in it.
* The part that does not depend on t keeps one summand for each oracle. A ghost name `fbw t k`
  counts only the searches that can reach its attempt: rounds with proof-of-work bits (`cTry`,
  Compile/Batch/Counts.lean), at most xGr of them. So the sum of (queries to the oracle)² over the
  ghost names is at most (the largest) * (the sum) ≤ xGr * xFbG (`Spec.sumSqBG`): the number of
  attempts occurs once, where a bound with a query bound for each oracle has its square, and beside
  it is the number of searches, not of all Fiat-Shamir queries.

  `xGr`   see its doc comment; coarse in `hashSqBG`: the largest is taken over all three tags
  `hashSqBG`   `hashSqBG W p n`: xTree² / 2^sMT + xTree² / 2^λ + (xFb² + xGr * xFbG) / 2^min(sFS, λ)
               + 3 xReq² / 2^λ
  `zetaHashBGTot`, `zetaBGTot`   see their doc comments

The statements.
  `Spec.supBG`   the maximum over the ten oracles and the ghost names of (marked queries) / 2^(bits
                 of the charged token) is at most `muB`
  `Spec.sumSqBG`   the second term of the lemma for a total query bound (`Rom.Spec.deferTotal`), at
                   the same counts and over the same set, is at most `hashSqBG`

At `L.grind` (Compile/Batch/TotalAtGrind.lean): `muB` is that of the record of protocols and wire
record before the transformer; `xGr` counts the searches of the rounds with b ≥ 1 and mo b ≥ 1.

Limits. Nothing at concrete parameters. The counts are worst cases (more + 1 attempts for each
search). Nothing about any scheme. No comparison with a bound that has a budget for each oracle
(`fbw` too) is proved here.
-/
import Compile.Batch.SpecGrind
import Compile.Batch.SpecTotal

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.GlueB (GCall SCall GAdm asW realW Close)
open Compile.BatchLife (LifeOutB LifeInB LifeB LifeAdmB)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The searches of setup and n batches, at most: the Fiat-Shamir queries that may have a second
attempt. (cTry 0: one for each slot in a round whose slot's query has proof-of-work bits with more ≥
1, one for the shared query likewise.) -/
def xGr (W : QueryLayout lam L) (p : Params) (n : ℕ) : ℕ :=
  cTry 0 1 L.offline.shape _ W.T.sh + p.leaves * cTry 0 1 L.link.shape _ W.Lk.sh +
    n * cTry 0 L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh

/-- the part of the hash terms that does not depend on the adversary's query bound: the number of
all attempts, xFbG, occurs once, times the number of searches -/
def hashSqBG (W : QueryLayout lam L) (p : Params) (n : ℕ) : ℝ≥0∞ :=
  (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ p.sMT +
    (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ lam +
    ((xFb (L := L) p n : ℝ≥0∞) * (0 + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
      (xGr W p n : ℝ≥0∞) * (xFbG W p n : ℕ) / 2 ^ (min p.sFS lam)) +
    3 * ((xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam)

/-- The overrun term and the hash terms of the scheme with proof-of-work bits, for one bound of t
queries, and n batches. -/
def zetaHashBGTot (W : QueryLayout lam L) (p : Params) (t n : ℕ) : ℝ≥0∞ :=
  p.leaves * binTail n p.leaves p.s1 + ((t : ℝ≥0∞) * muB W p n + hashSqBG W p n)

/-- ζ, the privacy bound: zetaHashBGTot and the three terms of the record of protocols -/
def zetaBGTot (W : QueryLayout lam L) (p : Params) (M : LH.Nums) : ℕ → ℕ → ℝ≥0∞ := fun t n =>
  zetaHashBGTot W p t n + (M.zT + p.leaves * M.zL + n * (L.maxBatchSize * M.zO))

/-- The first term of the lemma on deferred programming for a total query bound, at the counts of
the scheme with proof-of-work bits: its maximum is at most muB. -/
def Spec.supBG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p : Params) (n : ℕ),
    (Disc.osBG (maxMoreB W)).sup
        (fun o => (Disc.mAllB W p n o : ℝ≥0∞) / 2 ^ (Disc.rulesB W.K L lam p).bits o) ≤ muB W p n

/-- Its second term, at the same counts, is at most hashSqBG. -/
def Spec.sumSqBG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p : Params) (n : ℕ),
    ∑ o ∈ Disc.osBG (maxMoreB W), (Disc.mAllB W p n o : ℝ≥0∞) *
        (Disc.eAllB W p n o + Disc.mAllB W p n o : ℕ) / 2 ^ (Disc.rulesB W.K L lam p).bits o ≤
      hashSqBG W p n





end Compile.Batch
