-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Prog.lean: what a seed costs in ζ: the term `zS`; and, in words, what the scheme with
the objects of the implementation's three programs is (`argP`: Compile/Batch/StarS.lean) and what
the theorems on it do not say. One definition (words of this library: lean/GLOSSARY.md).
    `zS σ b`    for an oracle σ read as a source of coins (`SeedOracle`, Rom/SpecDerive.lean; its
                seeds are the elements of Fin (σ.sd + 1)) and a number b: the function of (t, n)
                with the value b + t / (σ.sd + 1), whatever n
  How it is meant. b is for the bias of the committer's large samples made from small ones; t /
  (number of seeds) for a guess of the seed among t queries. That is the use that the theorems make
  of it, not a statement of this file.
  Who uses it. The step from a committer that samples all its coins to one whose coins come from one
  seed (argBKE → argP): under the hypotheses of `stepSGr`, whatever bounds the scheme before has,
  the scheme after has α + b, ε, ζ + zS σ b: Compile/Batch/StepSGr.lean.
The two paragraphs that follow are by reading, on terms of other files.


What the scheme is. For every record of protocols L (three protocols Test, Link, Batch over
encodings of an index), wire records W, WP, parameters p, a way bk to make a large sample from small
ones and a reading σ of the oracle `other` as a source of coins, `argP W WP p bk σ`
(Compile/Batch/StarS.lean) is a commit-and-prove argument (C, P, V) in the syntax of ZKCP/Gen.lean
over the typed oracles of Compile/Batch/Oracles.lean:
    C (i)                 samples one seed. All other coins are answers of `other` at points made of
                          the seed and a label. With them it encodes i once as the first encoding
                          and p.M + 1 more times as copies, builds a salted Merkle tree over each
                          encoding, makes Test's proof string on the first encoding and Link's from
                          it to each copy.
         ivk = ((cm, piT), [(cm_0, piL_0), .., (cm_M, piL_M)])
             the first encoding's commitment, Test's proof string, and for each copy its commitment
             and Link's proof string
         isk = (i, seed)
    P (isk, requests)     samples a copy k, a placement of the requests in the L.maxBatchSize slots and the
                          coins of the batch, all fresh in every call; makes the node of copy k
                          again from (i, seed) (the randomness of its encoding, its salts, its tree;
                          not Link's proof string, and nothing of the first encoding); runs one
                          execution of Batch on it. For a slot without a request the leaf of the
                          request tree is a fresh uniform string of lam bits, and that sample is
                          all: no coins of a slot, no salt, no chain, no tree, no oracle query. A
                          proof is (k, piB): the number of the copy and the proof string of the
                          request's slot.
    V (ivk, x, (k, piB))  takes entry number k of ivk (it rejects if there is none: `VK_of_none`)
                          and runs the three compiled verifiers: Test on (cm, piT), Link on (cm,
                          cm_k, piL_k), Batch on (cm_k, x, piB) (`VK_of_some`). It does not read
                          p.M: the number of copies is the length of ivk's list (by reading: `reK`,
                          Compile/Batch/StarK.lean).
  The three algorithms written out: Compile/Batch/StarS.lean (`argP_C`, `argP_P`, `argP_V`:
  equalities by definition).
Limits:
  * This file proves nothing about a scheme. That `argP` has the three properties is neither stated
    nor proved in this library; the step from `argBKE` to it (`stepSGr`,
    Compile/Batch/StepSGr.lean) is an implication.
  * No theorem of this folder ties a term to a byte of the implementation. The scheme has the
    implementation's objects and their order of samples, by reading. Test, Link and Batch are
    variables here; at the model they are not the implementation's protocols.
    Differences at the level of this file that stay: a failed Test or Link is published as "none" in
    ivk, and V then rejects (the implementation publishes nothing and runs C again under a fresh
    seed, so its ivk has another distribution and its completeness error is not α); a rejection is
    the proof (k, none) and shows k (the implementation gives an empty file); p.M + 1 copies where
    the implementation says M.
  * The oracles are the typed family; the step to one oracle on strings (generic:
    `IsZKCPArgWith.overOne`, Rom/Carry.lean) is not applied to `argP` in this library; what it asks
    of the extractor: `extractorBK_local` (Top/Prog.lean), see its statement.
  * The definition is that of ZKCP/Gen.lean, which widens the definition of ZKCP/Defs.lean; what it
    follows: lean/CREDITS.md, "Further work". Completeness is for a batch fixed in advance.
  * Only the three properties are carried over. Perfect completeness, refined completeness, adaptive
    completeness, session-augmented index binding (for many proofs), extraction, the other requests
    of a batch hidden are not carried over by a `Carry` and are not claimed here for `argP`.
  * V reads one entry of ivk's list. The other entries and the length of the list are checked
    against nothing; a cheating committer may publish any list.
  * Under `WP.OK` (Iop/BatchWireP.lean), P's own coins (the copy, the placement, all coins and salts
    of a batch) are uniform and fresh. Nothing is said of a prover that derives them from a key.
  * isk is (i, seed) and nothing else. A prover that keeps parts of the copies' trees beside the
    seed, to save work, is another program with the same outputs (generic: Rom/Cache.lean; `argPL`:
    under the hypotheses of `Spec.lazyGr`, Compile/Batch/SeedLazyDefs.lean); no statement here is
    about it.
  * The oracle `other` is a random oracle. Nothing is said of a stream cipher or a pseudo-random
    function in its place.
  * Nobody counts batches: C, P and V do not read p.s1. `zetaHashBGTot`
    (Compile/Batch/SpecTotalG.lean: p.leaves * binTail n p.leaves p.s1, with p.leaves = p.M + 1:
    Compile/Spec.lean) holds the overrun term (p.M + 1) · Pr[Bin(n, 1 / (p.M + 1)) > p.s1]; where
    that is near 1, ζ says nothing.
  * Sizes, numbers of queries, running times: not here.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.StarS
import Rom.Carry
import Compile.Batch.CompleteRefStarG
import Compile.Batch.CompleteUnifG
import Compile.Batch.DisciplineChainAll
import Compile.Batch.EqBatch
import Compile.Batch.EqProve
import Compile.Batch.EqSetup
import Compile.Batch.GlueBinding
import Compile.Batch.GluePrivacy
import Compile.Batch.HonestK
import Compile.Batch.HopTot
import Compile.Batch.Late4
import Compile.Batch.LifeStar
import Compile.Batch.PubDefer
import Compile.Batch.PubLate
import Compile.Batch.PubLump
import Compile.Batch.PubOverrun
import Compile.Batch.Sound
import Compile.Batch.SpecPubGr

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## The bounds -/

/-- what the seed costs in ζ: the bias b of the committer's large samples, and a guess of the
seed -/
def zS {S : OSpec} (σ : SeedOracle S) (b : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞ := fun t _ =>
  b + (t : ℝ≥0∞) / (σ.sd + 1 : ℕ)


end Compile.Batch
