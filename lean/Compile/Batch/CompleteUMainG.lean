-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUMainG.lean: completeness of the compiled scheme with free empty slots (no
query for an empty slot: `proveBU`, Compile/Batch/ProverU.lean) whose rounds may have proof-of-work
bits (words of this library: lean/GLOSSARY.md).

    theorem completeBatchUGr : Spec.completeBatchUGr
    (Compile/Batch/SpecUGr.lean)

For every record of protocols L with `L.PropsNoAcc`, every wire record W with `W.OKG`,
`GrFitB W Ryes`, `WP.OK` and the format `Fmt`: `argBU W WP p` has completeness error at most
`alphaBG W M` for batches of at most `L.maxBatchSize` requests. The proof combines, each under the hypotheses
of its statement:
 * `acceptsHonestBUG` (Compile/Batch/CompleteUChain.lean, Compile/Batch/CompleteUAcc.lean): for
   fixed oracle functions, V accepts unless Test, the Link of the sampled copy or the slot is bad.
 * `lawTUG`, `lawLUG`, `lawBUG` (Compile/Batch/CompleteURef.lean,
   Compile/Batch/CompleteURefStarG.lean): for fixed oracle functions, each of these events has the
   distribution of a small experiment.
 * `unifTG`, `unifLG`, `unifBUG` (Compile/Batch/CompleteUnifG.lean,
   Compile/Batch/CompleteUUnifG.lean): under lazily sampled oracles, each small experiment shows
   "bad" with probability at most a bound on that of the withheld set plus that of a failed search.
 * `completeOfUG` (Compile/Batch/CompleteUG.lean): the union bound.

Limits: what the heads of Compile/Batch/SpecUGr.lean and Compile/Batch/SpecGrind.lean list as not
said is not said here either. Among these (the head of Compile/Batch/SpecUGr.lean): nothing about
the mean number of attempts; a batch is still counted as maxBatchSize full slots, each with all its searches,
however few requests it holds.
-/
import Compile.Batch.CompleteUG
import Compile.Batch.CompleteUAcc
import Compile.Batch.CompleteURefStarG
import Compile.Batch.CompleteUUnifG

namespace Compile.Batch

/-- Completeness of the compiled scheme with free empty slots whose rounds may have proof-of-work
bits (`Spec.completeBatchUGr`). -/
theorem completeBatchUGr : Spec.completeBatchUGr :=
  completeOfUG acceptsHonestBUG lawTUG lawLUG lawBUG unifTG unifLG unifBUG

end Compile.Batch
