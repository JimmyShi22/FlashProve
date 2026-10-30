-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ZeroRunMass.lean: the chance of the exception at flashProveAtFiles.

1.  WHAT IS CLAIMED: at the compiler's own honest side at flashProveAtFiles, for any provers and starts: over all coins, under every hash function,
    the key's offline string or the online string has a first salt in Zs, or reads a run value in BadValue, with chance at most
    2 · 2^-sFS and the coins' two chances of BadValue: γ written out.
2.  Premises: the provers send their run values, at every index; the readers do not read nonces. Zs holds at most one string of sFS bits.
3.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import VerifiableInference.Final.ZeroSaltMass
import Johnson.CompletenessAndZeroKnowledge.TheSettingsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles OnBytes.WholeKey OnBytes.FrontRoad OnBytes.Prover
open VerifierAndGoals FlashProve FlashProve
open Prob
open IntegerTransformer (Settings)

variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers) (limits : SearchLimits)
  (slotSalts : RequestLeafSaltLayout)

/-- The honest side at a value of the reading. -/
abbrev flashSide (reading : FlashReading files) :=
  (honestSide (flashLayout files settings fallbackInstance reading) provers
    (theSettings files settings fallbackInstance provers starts limits slotSalts reading)).side

/-- **THE MASS OF THE EXCEPTION AT flashProveAtFiles.** -/
theorem flash_bad_mass
    (hRun : ∀ reading, RunValuesAreSent (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers starts limits slotSalts reading) fun _ => True)
    (hN : ∀ reading, ReadsThroughNonces (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers starts limits slotSalts reading))
    (Zs : Set Rom.Bits)
    (hZ : ∀ a b : Fin (flashProveDescription.input files allZeroDigest []).compilerParameters.sFS → Bool, List.ofFn a ∈ Zs → List.ofFn b ∈ Zs → a = b)
    (offlineBad : OneProtocolProof 256 (batTC (flashProveDescription.input files allZeroDigest []).protocol (flashProveDescription.input files allZeroDigest []).offlineRoundSplits) → Prop)
    (onlineBad : OneProtocolProof 256 (flashProveDescription.input files allZeroDigest []).protocol.onlineBatch → Prop) (BadValue : starts.RunValues → Prop)
    (hOffline : ∀ a, offlineBad a → BadValue (starts.readOffline a.plains))
    (hOnline : ∀ b, onlineBad b → BadValue (starts.readOnline b.plains)) {εOffline εOnline : ℝ≥0∞}
    (massOffline : pr (unif provers.offlineProver.Coin) {κ | BadValue (starts.runValuesOffline κ)} ≤ εOffline)
    (massOnline : pr (unif provers.onlineProver.Coin) {κ | BadValue (starts.runValuesOnline κ)} ≤ εOnline)
    (i : (flashProveDescription.input files allZeroDigest []).Index) (x : (flashProveDescription.input files allZeroDigest []).Instance) :
    ZKCP.Pr (badExp (readOne (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
        (flashSide files settings fallbackInstance provers starts limits slotSalts)) i x ())
        (fun _ => {o | EitherBad (fun a => a.salt ∈ Zs) offlineBad (fun b => b.salt ∈ Zs) onlineBad o.1.1.2 o.2}) ≤
      (((2 : ℝ≥0∞) ^ (flashProveDescription.input files allZeroDigest []).compilerParameters.sFS)⁻¹ + εOffline) +
        (((2 : ℝ≥0∞) ^ (flashProveDescription.input files allZeroDigest []).compilerParameters.sFS)⁻¹ + εOnline) :=
  eitherBad_mass _ _ i x _ _ _ _
    (fun g reading => small_commitW_salt _ _ _ _ g i Zs
      (honestSide_salt_offline (flashLayout files settings fallbackInstance reading) provers _ Zs hZ))
    (fun g reading => Small.weaken (fun k ⟨a, ha, hb⟩ => ⟨a, ha, hOffline a hb⟩)
      (small_commitW_read g (hRun reading) (hN reading) i BadValue massOffline))
    (fun g reading isk => small_proveW_salt _ _ _ _ g isk x Zs
      (honestSide_salt_online (flashLayout files settings fallbackInstance reading) provers _ Zs hZ))
    (fun g reading isk => Small.weaken (fun k ⟨b, hb, hc⟩ => ⟨b, hb, hOnline b hc⟩)
      (small_proveW_read g (hRun reading) (hN reading) isk x BadValue massOnline))

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.flash_bad_mass
