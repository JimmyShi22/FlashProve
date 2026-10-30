-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecOneCallL.lean: the counts (of hash blocks asked for) for the committers of `argP`
and `argPL` and for the lazy prover of `argPL`, under the rule `ruleT` (block 0 first:
Compile/Batch/SpecOneCall.lean). Terms. Nothing is proved here. (Words of this library:
lean/GLOSSARY.md.)

`cCPA`, `cCPLA`, `cPLA` are sums over `cCBA` and `cPUA` (Compile/Batch/SpecOneCall.lean), in which a
failed proof-of-work attempt that is not the last costs one. `argP` has one seed
(Compile/Batch/StarS.lean); `argPL` has also the cache and the lazy prover
(Compile/Batch/SeedLazyDefs.lean).

Why only `cCBA` and `cPUA` have a summand for failed attempts: only the Fiat-Shamir part has a
search; the trees, the coins derived under the seed, the cache and the openings have none.

What is proved of them.
(1) Compile/Batch/OneCallCostPL.lean proves, for every weight that meets `TryW`
(Compile/Batch/OneCallCostW.lean), `cav_C_argSeed`, `cav_C_argPL`, `cav_P_argPL` with the sums
`cCPW`, `cCPLW`, `cPLW`;
(2) and `cCPW_one`, `cCPLW_one`, `cPLW_one`: at ca = 1, bf t i = nb t i + 1 those sums are `cCPA`,
`cCPLA`, `cPLA`.
(3) The rule's own weight meets `TryW` at these two (`tryW_numA`), if the encoding splits an answer
as Compile/Batch/ImplOf.lean does (`Std m`) and the proof-of-work checks depend on block 0 alone
(`Test0 W`).
Hypotheses of the three theorems of (1): `W.OKG`; a round with proof-of-work bits has a marked block
(`NbPos W nb`: there nb t i is at least 1); the seed oracle σ reads the oracle `other` (σ.o =
`OracleName.other`); for P also: a slot's verifier reads at most nE positions of the encoded index, and each
stored level of the key has at most 2^(depth − ℓ) digests. They are on the schemes before their sets
of paths are pruned.
Marked: named by the table `needOf nb m`, Compile/Batch/NeedTable.lean: the first nb t i blocks of a
Fiat-Shamir answer of round i of protocol t, and the chaining value; everywhere else: all.

Notation: `WP`: a `WireBP L` (Iop/BatchWireP.lean): "the prover's data for the three protocols, and
the enumeration of the encoding randomness"; `bk`: a `CoinPlan` (Rom/Blocks.lean): "how a uniform
sample is made from small ones"; natural numbers, or functions into them: `bk.m`: "the number of
small samples for a sample with n + 1 outcomes"; `p.M`: "the number of copies is M + 1" (`Params`,
Compile/Star.lean); `off`: "the weighted number of samples of C before copy j"; `cNode`: "the
weighted number of samples of a `Node`" (both: Compile/Batch/SeedStar.lean); `tr d`: "the leaves and
the inner nodes of a tree of depth d" (Compile/Batch/NeedCostTree.lean); `cOpL`: "what one opening
costs the lazy prover" (Compile/Batch/NeedCostPL.lean); `ℓ`, `nE`, `n`: natural numbers; `ca`: a
natural number; `bf`: a function Tag → ℕ → ℕ; in `TryW W nb m wt ca bf`
(Compile/Batch/OneCallCostW.lean, where `ca` is called a): "what a failed attempt that is not the
last weighs at most"; "what any Fiat-Shamir query of round i of protocol t weighs at most (with
proof-of-work bits: if the table marks a block there)"; the cache: `Ca`
(Compile/Batch/SeedCache.lean): "The cache: for each copy the root of its tree and the digests of
one level."

Limits: statements that on every path the blocks that the rule asks of C, of P, add up to at most
these sums are not in this library. The same sums for the table of the second exit (the step to one
hash function that asks only for marked blocks, Rom/OverOneN.lean), in which every attempt of a
search is charged all marked blocks of its round, are not in this library. Worst case over the
oracle still: every search at its cap. This file says nothing on the mean, and nothing on V. No
numeral.
-/
import Compile.Batch.SpecOneCall
import Compile.Batch.NeedCostPL

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (needOf tr Std cOpL)
open Compile.Batch.Seed (off cNode argPL Ca)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (nb : Tag → ℕ → ℕ) (bk : CoinPlan)

/-- The count for the committer of `argP` (one seed). -/
def cCPA : ℕ := cCBA W p nb + off W WP p bk.m (p.M + 1)
/-- The count for the committer of `argPL`, which also computes the cache. -/
def cCPLA : ℕ := cCPA W WP p nb bk + (p.M + 1) * (tr W.depth + cNode W WP p bk.m)
/-- The count for the lazy prover of `argPL`, on a batch with n requests. -/
def cPLA (ℓ nE n : ℕ) : ℕ :=
  (2 ^ (W.depth - ℓ) - 1) + bk.m WP.ri.n + cPUA W nb n + n * (nE * cOpL p bk ℓ)

end Compile.Batch
