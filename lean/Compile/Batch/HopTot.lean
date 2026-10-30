-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/HopTot.lean: an instance of `HopB` (Compile/Batch/SpecHop.lean, whose header says what
the parameter is for): a bound on the game hop of deferred programming (`hashTermsBGTot`, below). It
is for one bound on all the adversary's queries, at the counts of the compiled scheme whose rounds
may have proof-of-work bits.
  `hopB_total : HopB W p (hashTermsBGTot W p)`
      from the lemma on deferred programming `hopCost_total` (Rom/HopCost.lean) and the counts
      `deferTot_counts` (Compile/Batch/TotalG.lean). In hashTermsBGTot W p t n = t * muB W p n +
      hashSqBG W p n no number of attempts occurs in the part linear in t
  `zetaBGTot_eq_gen`      `zetaBGTot W p M` is `zetaBGen` at `hashTermsBGTot W p`
It holds for every wire record and all parameters, without hypotheses: it is about counts and about
that lemma, not about any challenger.

Notation: `t`, `n`: natural numbers; in `zetaHashBGTot W p t n` (Compile/Batch/SpecTotalG.lean): one
bound of t queries, and n batches; `M`: an `LH.Nums` (Iop/InteractiveOracleProof.lean): all numbers of the interface;
`muB W p n` (Compile/Batch/SpecTotal.lean): meant as a bound on the probability that one query of
the adversary hits a marked query, whichever oracle it goes to; `hashSqBG W p n`
(Compile/Batch/SpecTotalG.lean): the part of the hash terms that does not depend on the adversary's
query bound; `binTail n m s` (Compile/Spec.lean): Pr[Bin(n, 1/m) > s], as an exact finite sum;
`zetaHashBGTot` (Compile/Batch/SpecTotalG.lean): the overrun term and the hash terms of the scheme
with proof-of-work bits; `zetaBGTot` (the same file): `zetaHashBGTot` and the three terms of the
record of protocols; `HopB W p h` (Compile/Batch/SpecHop.lean): `HopBAt` at the counts of the scheme
that hashes every slot: one setup and n batches of maxBatchSize slots.

Limits: nothing on any sequence of experiments, nothing for a form of the scheme with other counts,
nothing at concrete parameters.
-/
import Compile.Batch.SpecHop
import Rom.HopCost
import Compile.Batch.TotalG

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The bound on the hop, for one bound on all the adversary's queries. -/
def hashTermsBGTot (W : QueryLayout lam L) (p : Params) (t n : ℕ) : ℝ≥0∞ :=
  (t : ℝ≥0∞) * muB W p n + hashSqBG W p n

theorem zetaHashBGTot_eq (W : QueryLayout lam L) (p : Params) (t n : ℕ) :
    zetaHashBGTot W p t n = p.leaves * binTail n p.leaves p.s1 + hashTermsBGTot W p t n := rfl

theorem zetaBGTot_eq_gen (W : QueryLayout lam L) (p : Params) (M : LH.Nums) :
    zetaBGTot W p M = zetaBGen L p M (hashTermsBGTot W p) := rfl


/-- The instance for one bound on all the adversary's queries. -/
theorem hopB_total (W : QueryLayout lam L) (p : Params) : HopB W p (hashTermsBGTot W p) := by
  intro n
  refine Rom.HopCost.mono
    (c := Rom.costTotal (S := spec lam W.K L) (Disc.eAllB W p n) (Disc.mAllB W p n)
        (Disc.rulesB W.K L lam p).bits (Disc.osBG (maxMoreB W)))
    (Rom.hopCost_total (S := spec lam W.K L) _ _ _ _) fun t => ?_
  unfold Rom.costTotal hashTermsBGTot
  exact deferTot_counts W p t n

end Compile.Batch
