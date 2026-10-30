-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/Prog.lean: if the query encoding `m` gives the leaf and the node oracle one hash block each, the
extractor of the scheme with the entries in the key (`extractorBK`, Compile/Batch/StarK.lean) reads
entries of one-block oracles only. (Terms: lean/GLOSSARY.md.)
  `extractorBK_local`   That statement, as `LocalTo` (Rom/Family.lean), which the step to one oracle
                        asks of the extractor.
Limits: This file defines no scheme and states no theorem on a scheme.
-/
import Compile.Batch.StepL
import Compile.Batch.CompleteU
import Compile.Batch.MainKEGr
import Compile.Batch.Prog

noncomputable section

namespace Top.Prog
open Iop Rom ZKCP Compile Compile.Batch
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The extractor of the scheme with the entries in the key reads entries at one-block oracles only
(`LocalTo`), if `m` gives `leaf` and `node` one block each. -/
theorem extractorBK_local (W : QueryLayout lam L) (m : OracleCoding (Compile.Batch.spec lam W.K L) lam)
    (hl : m.blocks Compile.Batch.OracleName.leaf = 1) (hn : m.blocks Compile.Batch.OracleName.node = 1) :
    LocalTo (extractorBK W) m :=
  ⟨fun v tr => (extractorB_local W m hl hn).1 v.1 tr, fun _ _ _ _ _ => rfl⟩

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
  (σ : SeedOracle (Compile.Batch.spec lam W.K L)) (m : OracleCoding (Compile.Batch.spec lam W.K L) lam)



variable {W WP p bk σ m}



end Top.Prog
