-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubProgMainGr.lean: one lemma. This file does not prove index privacy of any scheme
(see Compile/Batch/PubProgMainBGr.lean).

  `safeFPp`  If L.maxBatchSize = 2 ^ W.depthReq, `Pp` obeys the rules of deferred programming, for all flags
             (for which requests a proof string is made: `FProg`, Compile/Batch/PubProg.lean)
             (`Disc.safePB`).
Notation: the rules of deferred programming: the list "Rules:" in the head of Rom/Defer.lean;
`SafeFProg W p pq`: for all flags fr, `SafeProg`: the program obeys the rules, with the counts of
one batch (Compile/Batch/PubProgModeI.lean, Compile/Batch/CloseProg.lean); `L.maxBatchSize`: the number of
slots (Iop/Batch.lean); `W.depthReq`: depth of a request tree (Iop/BatchWire.lean).
-/
import Compile.Batch.EqBatch
import Compile.Batch.EqProve
import Compile.Batch.EqSetup
import Compile.Batch.GluePrivacy
import Compile.Batch.GrOK
import Compile.Batch.HopTot
import Compile.Batch.Late4
import Compile.Batch.LifeStar
import Compile.Batch.PubDefer
import Compile.Batch.PubLate
import Compile.Batch.PubLump
import Compile.Batch.PubOverrun
import Compile.Batch.PubProgModeI
import Compile.Batch.PubProgVia
import Compile.Batch.SpecPubGr

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.GlueB (GCall SCall GAdm asW realW simOf viaCP Close)
open Compile.BatchLife (LifeOutB LifeInB LifeB LifeAdmB Sims simWorldB lifeStarBWith)
open scoped ENNReal

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- if L.maxBatchSize = 2 ^ W.depthReq: the prover's program of the compiled scheme obeys the rules, for all
flags -/
theorem safeFPp (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hN : L.maxBatchSize = 2 ^ W.depthReq) :
    SafeFProg W p (Pp W WP p) :=
  fun fr k xs d hd hk => Disc.safePB I X lam L W WP p k fr xs d hN hd hk


end Compile.Batch
