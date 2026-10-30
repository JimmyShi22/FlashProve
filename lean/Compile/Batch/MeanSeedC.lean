-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/MeanSeedC.lean: the computation of the cache queries no Fiat-Shamir oracle, if the
  seed's oracle is `OracleName.other` (Compile/Batch/Oracles.lean).
    `onlyQ_cacheFrom`    no query of `cacheFrom` (Compile/Batch/SeedCache.lean) goes to `fb t`, for
                         every protocol t (`OnlyQ`, `NotFb`: Compile/Batch/CompleteUnif.lean)
  Limits: nothing on a mean: statements on the mean weight of the queries of the committers with a
  seed are not in this library.
-/
import Compile.Batch.SeedMain
import Compile.Batch.MeanSeed
import Compile.Batch.NeedCostPL

noncomputable section

open scoped ENNReal

namespace Compile.Batch
open Iop Rom Prob ZKCP

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

namespace MeanSeedC
open Seed Compile.Seed MeanSeed CompleteUnif

variable (W : QueryLayout lam L)
  (WP : WireBP L) (p : Params) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-- If the seed's oracle is `other`, the cache queries no Fiat-Shamir oracle. -/
theorem onlyQ_cacheFrom (hσ : σ.o = OracleName.other) (t : Tag) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) :
    ∀ js, OnlyQ (S := spec lam W.K L) (NotFb t) (cacheFrom W WP p bk σ ℓ k js)
  | [] => trivial
  | _ :: js =>
    OnlyQ.bind (onlyQ_derived W bk σ hσ t (nf_nodeP' W WP p k.1) [] k.2 _) fun _ =>
      OnlyQ.bind (onlyQ_cacheFrom hσ t ℓ k js) fun _ => trivial

end MeanSeedC




open MeanSeedC Seed



end Compile.Batch
