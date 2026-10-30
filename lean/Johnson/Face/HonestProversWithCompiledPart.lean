-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/HonestProversWithCompiledPart.lean: the final statement, of the protocol's honest provers.

 1. honestProvers (E2E/TheHonestProver.lean) is the protocol's three provers, at the public files.
 2. It is a function of the key file's arguments, Parts.
 3. theProvers are those, refusing where the request is not served: served depends on the weights.
 4. ServedAt is the relation at which completeness and zero knowledge at the interactive level are read,
    by servedAt_eq: it holds only of built instances.
 5. At a request that builds no instance the prover runs at neverBuiltRequest, which no request builds
    and ServedAt does not hold of: so no proof goes out there, whatever the weights.
 6. CompiledPart is what compilation adds: search limits, salts, the coins' numbers.
 7. honestProversAndSettingsAtFiles lays the two together, and TheFinalStatement is FinalStatement of that honest part.
-/
import Johnson.Face.FinalStatement
import Johnson.Face.NeverBuilt
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve VerifiableInference.OnPublicFiles OnBytes.FrontRoad OnBytes.WholeKey
open TypedOracleCompiler.Compile.Batch.Cms AtPublicFiles.AtFiles.HonestTerm
open _root_.Iop hiding GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open IntegerTransformer (Settings)
open scoped ENNReal

/-- The protocol's honest provers, which refuse where the request is not served. -/
def theProvers (files : PublicFiles) (settings : Settings) (parts : Parts files) :
    HonestProvers ((flashProveDescription.F files).withProvers (flashProveDescription.P files)) :=
  HonestProvers.refuseUnserved
    ⟨(honestProvers files parts).T, (honestProvers files parts).Lk, (honestProvers files parts).B⟩
    (ServedAt files settings)

/-- What compilation adds to them, at public files and settings. -/
structure CompiledPart (files : PublicFiles) (settings : Settings) (parts : Parts files) where
  /-- What the honest side chooses beside the provers, at each value of the public reading. -/
  compiledSettings : (reading : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D) →
    CompiledSettings ((flashProveWiring files settings neverBuiltRequest).layoutAtReading reading)
      (theProvers files settings parts)
  /-- The honest committer samples one number from 0 to this. -/
  coinBound : ℕ
  /-- The sessions that one copy bears. -/
  onlineRunsPerCopy : ℕ

/-- **The honest part of flashProveAtFiles**, made of the protocol's honest provers. -/
def honestProversAndSettingsAtFiles (files : PublicFiles) (settings : Settings) (parts : Parts files)
    (compiled : CompiledPart files settings parts) : HonestProversAndSettingsAtFiles files settings where
  fallbackInstance := neverBuiltRequest
  provers := theProvers files settings parts
  compiledSettings := compiled.compiledSettings
  coinBound := compiled.coinBound
  onlineRunsPerCopy := compiled.onlineRunsPerCopy

/-- **The final statement of the protocol's honest provers.** It takes the key file's arguments, the
compiled part and the error: no value of the first two is given here. -/
abbrev TheFinalStatement (parts : (files : PublicFiles) → Parts files)
    (compiled : (files : PublicFiles) → (settings : Settings) → CompiledPart files settings (parts files))
    (zeroKnowledgeError : ℝ≥0∞) : Prop :=
  FinalStatement (fun files settings => honestProversAndSettingsAtFiles files settings (parts files)
    (compiled files settings)) zeroKnowledgeError

end VerifiableInference.Compilation
