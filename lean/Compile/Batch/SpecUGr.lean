-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecUGr.lean: completeness of `argBU`, whose prover makes no query for an empty slot,
for records of protocols whose rounds may have proof-of-work bits. (The entries in the key, with
such bits: Compile/Batch/SpecPubGr.lean.) One statement, `Spec.completeBatchUGr`: the completeness
error is `alphaBG`, without a hash term. Nothing is proved here. The proof:
Compile/Batch/CompleteUMainG.lean. (Words of this library: lean/GLOSSARY.md.)

What a round with proof-of-work bits is, the hypotheses `L.PropsNoAcc`, `W.OKG`, `GrFitB` (the
statement also has `WP.OK` and the format) and the bound `alphaBG`: header of
Compile/Batch/SpecGrind.lean. The scheme is `argBU` (Compile/Batch/StarU.lean), at a wire record
with proof-of-work records. In it C and `PU` are `realQ` (Compile/Batch/Oracles.lean: queries to
ghost names `fbw` become queries to `fb`) of what `erase` makes of the token programs. An empty slot
runs no search in `PU`: it has no chain at all.

Limits: what the head of Compile/Batch/SpecGrind.lean lists as not said is not said here either.
Only completeness of `argBU` is stated here. Nothing about the mean number of attempts. A batch is
still counted as maxBatchSize full slots, each with all its searches at the worst case, however few requests it
holds.
-/
import Compile.Batch.SpecGrind
import Compile.Batch.SpecPubGr
import Compile.Batch.HopTot
import Compile.Batch.GhostGuards
import Compile.Batch.StarKE

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.GlueB Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params)

namespace Spec

/-- Completeness of `argBU`, without a hash term (hypotheses below). -/
def completeBatchUGr : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M),
    W.OKG → GrFitB W Ryes → WP.OK → L.onlineBatch.ann.Fmt →
    Gen.HasCompletenessError (relPair Ryes Rno h.sub) (argBU W WP p) L.maxBatchSize (alphaBG W M)



end Spec


end Compile.Batch
