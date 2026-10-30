-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ReadsAtPlug.lean: the format's readers do not read nonces.

1.  WHAT IS CLAIMED: at flashProveAtFiles, where the settings' readers are the two values pvKey and pvZ, two transcripts that are one but for nonces
    read alike: law_cuts, since no nonce stands in the join or the seam.
2.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import VerifiableInference.Final.ZeroSaltMass
import Johnson.CompletenessAndZeroKnowledge.FormatStarts
import E2E.BridgeTied
import E2E.KeyBridgeFilled
import Johnson.Prover.Print.StratLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles OnBytes.WholeKey OnBytes.FrontRoad OnBytes.Prover
open VerifierAndGoals FlashProve FlashProve
open AtPublicFiles.AtFiles AtPublicFiles.Bridge
open Johnson.Prover.Print
open IntegerTransformer (Settings)

variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (rounds : FormatRounds)
  (runsOffline : provers.offlineProver.Coin → FormatRuns) (runsOnline : provers.onlineProver.Coin → FormatRuns)
  (linkRuns : FormatRuns) (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout)

/-- The format's starts at the readers of the plain parts. -/
abbrev pvStarts : SaltStarts provers :=
  formatStarts provers rounds runsOffline runsOnline linkRuns
    (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀) (pvZ files (dataAtFiles flashProveData files).P)

/-- **The readers of the format do not read nonces.** -/
theorem readsThroughNonces_pv (reading : FlashReading files) :
    ReadsThroughNonces (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers
        (pvStarts files provers rounds runsOffline runsOnline linkRuns) limits slotSalts reading) where
  offline := fun cap τ τ' h => by
    obtain ⟨eJ, e3, -⟩ := law_cuts _ _ _ cap _ _ _ _ τ τ' h
    show pvKey _ _ τ'.plains = pvKey _ _ τ.plains
    exact Prod.ext
      (congrArg Compile.Joined.JoinMsg.run ((plJ_plains _ τ').trans (eJ.trans (plJ_plains _ τ).symm)))
      ((pl3_plains _ τ').trans (e3.trans (pl3_plains _ τ).symm))
  online := fun cap τ τ' h => by
    obtain ⟨eJ, e3, -⟩ := law_cuts _ _ _ cap _ _ _ _ τ τ' h
    show pvZ _ _ τ'.plains = pvZ _ _ τ.plains
    exact Prod.ext
      (congrArg Compile.Joined.JoinMsg.run ((plJ_plains _ τ').trans (eJ.trans (plJ_plains _ τ).symm)))
      ((pl3_plains _ τ').trans (e3.trans (pl3_plains _ τ).symm))

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.readsThroughNonces_pv
