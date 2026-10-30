-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecEq.lean: the honest program in the language `LStep` (Rom/DeferLate.lean) has the
distribution of the lifetime experiment's sessions (Compile/Batch/SpecLifeStar.lean) followed by the
reduction's program (`CpW`, `PpW`: Compile/Batch/Mirror.lean; the reduction: `wrapBP`,
Compile/Batch/PubWr.lean). Statements only. (Words of this library: lean/GLOSSARY.md.)

  `Spec.eqSetupB`   the setup. Of the true key only the index, `keyOf` and the encoding randomness
                    of the copies are compared: the rest is never read again
  `Spec.eqBatchB`   a batch with an own request (one of the adversary's; `hasOwn b`) and at most maxBatchSize
                    requests (`b.pairs.length ≤ L.maxBatchSize`), once the copy is sampled (j, `lf`), with
                    token numbers shifted (`virtL N₀ δ`).
                    On the left the honest program does the hash work of all slots, makes proof
                    strings for the own requests, and the reply keeps their proofs (`PpLJ`,
                    `replyOf`);
                    on the right the experiment is told only these requests, places them, and the
                    reduction makes their proofs from what the experiment returns (`placeB`, `PpW`)

Both state, under hypotheses, equalities of distributions of (reply, state of the experiment). Both
are used by lumpBP (Compile/Batch/PubLump.lean).
-/
import Compile.Batch.ChallL
import Compile.Batch.SpecLifeStar
import Compile.Batch.SpecFit
import Iop.BatchFmt

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.BatchLife (linksGB placeB bsess vec)
open Compile.Lifetime (sess)
open Compile.DefC (virtL)

/-- The setup. -/
def Spec.eqSetupB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (i : I) (st : LSt (spec lam W.K L)),
    L.Wired → W.OKG → GrFitPB W → WP.OK →
    ((CpL W WP p i).run st).map
        (fun y => ((y.1.1, y.1.2.i, keyOf y.1.2, y.1.2.leaves.map fun lf => lf.node.r), y.2)) =
      (unif L.EncodingRandomness).bind fun r₀ => (sess L.honestOfflineProver (i, r₀) ()).bind fun sT =>
          (linksGB (fun r r' => sess L.honestLinkProver (i, r, r') ()) r₀ (p.M + 1)).bind fun ls =>
            ((CpW W p sT (ls.map Prod.snd)).run st).map fun y =>
              ((y.1.1, i, y.1.2, ls.map Prod.fst), y.2)

/-- A batch, once the copy is sampled. -/
def Spec.eqBatchB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (N₀ δ : ℕ) (k : IskH lam L) (b : ZKCP.Gen.Batch X Unit) (j : Fin (p.M + 1))
      (lf : LeafRec lam L) (st : LSt (spec lam W.K L)),
    L.Wired → L.onlineBatch.ann.Coherent → L.onlineBatch.ann.Fmt → W.OKG → GrFitPB W → WP.OK →
    k.leaves[j.val]? = some lf → hasOwn b = true → b.pairs.length ≤ L.maxBatchSize →
    ((virtL N₀ δ (PpLJ W WP p k (ownFlag b) (reqs b) j)).run st).map
        (fun z => (replyOf b z.1, z.2)) =
      (placeB L (fun J xs rest => bsess L.honestOnlineBatchProver (k.i, lf.node.r) (vec J xs rest) J)
        b.ownX).bind fun ret =>
          ((virtL N₀ δ (PpW W p (keyOf k) b.ownX j.val ret)).run st).map fun z =>
            ((.inr z.1 : BIn lam L), z.2)

end Compile.Batch
