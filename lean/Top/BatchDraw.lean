-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/BatchDraw.lean: the record of protocols with challenges derived from hash blocks by any
challenge samplers (`LBd`), with its wire records (`WBd`, `WPBd`) and numbers (`numsDraw`). (Terms:
lean/GLOSSARY.md.) A record of protocols, `BatchProtocol` (Iop/Batch.lean), holds an encoder, a decoder and
the protocols Test, Link and Batch. The verifier's wire record (`QueryLayout`, Iop/BatchWire.lean) is what
the compiler (Compile/) needs beside `BatchProtocol` in order to write down the compiled batch verifier as a
term; the prover's (`WireBP`, Iop/BatchWireP.lean) is what the compiled prover needs beside it. The
rounds' samplers (Iop/Draw.lean) are a datum `dr : L.Draws lam` beside `L : BatchProtocol I X`.
  `numsDraw`            The numbers of `LBd` (`Spec.drawsPropsB`, Iop/BatchWireDraw.lean): the round
                        error × κ₀^(largest number of blocks of a round); the abort probabilities
                        and the errors of simulation of Test and Link × κ₀^n; Batch's error of
                        simulation × (κ₀^n)^N. κ₀ is the bias of one block, n a bound on the blocks
                        of all rounds of a protocol, N the number of slots.
Notation: `M : LH.Nums`: all numbers of the interface (Iop/InteractiveOracleProof.lean); `dr.K`: the largest number
of hash blocks of a round; slot: one of the places of a batch (lean/GLOSSARY.md).
Limits: This file does not define the scheme over these samplers and does not prove that scheme's
theorem.
-/
import Iop.BatchWireDrawOK
import Compile.Batch.CompleteRefStarG
import Compile.Batch.CompleteUnifG
import Compile.Batch.DisciplineChainAll
import Compile.Batch.EqBatch
import Compile.Batch.EqProve
import Compile.Batch.EqSetup
import Compile.Batch.GlueBinding
import Compile.Batch.GluePrivacy
import Compile.Batch.HopLate
import Compile.Batch.HopTot
import Compile.Batch.Late4
import Compile.Batch.LifeStar
import Compile.Batch.Lump
import Compile.Batch.OverrunGen
import Compile.Batch.Ser
import Compile.Batch.Sound
import Compile.Batch.WithinVCB
import Iop.BatchPullFmt
import Iop.SerBPull

noncomputable section

namespace Top.Batch
open Iop Rom ZKCP Compile Compile.Batch
open scoped ENNReal

variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (dr : L.Draws lam) (ax : L.Aux pT pL pB)

/-- `L` with challenges derived from hash blocks. -/
abbrev LBd : BatchProtocol I X := L.draws dr
abbrev WBd : QueryLayout lam (LBd lam L dr) := QueryLayout.ofDraws lam L pT pL pB z no dr ax
abbrev WPBd : WireBP (LBd lam L dr) := WireBP.ofDraws lam L pT pL pB dr ax

/-- The numbers of `LBd` (`Spec.drawsPropsB`, Iop/BatchWireDraw.lean). -/
def numsDraw (M : LH.Nums) (κ₀ : ℝ≥0∞) (n : ℕ) : LH.Nums := M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize


end Top.Batch
