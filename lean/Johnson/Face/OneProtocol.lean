-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/OneProtocol.lean: the three statements on the interactive protocol, of one
protocol.

 1. Soundness, completeness and zero knowledge stand at one term: the protocol at the public files.
 2. Completeness and zero knowledge are read at one relation, the served requests, at the same
    proof-of-work bits, and of one term: the protocol's honest provers under that relation.
 3. Soundness is read at a wider relation, and of every prover: it holds of these provers too.
 4. The served requests lie inside that wider relation.
 5. All are meant at public files in scope that pass the test: the files in use.
 6. That this file compiles is the check: all three come from one library, in one build.
-/
import Johnson.Face.HonestProversWithCompiledPart
import E2E.SoundAsIOPAtFiles
import E2E.CompleteAsIOPAtFiles
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocol

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open scoped ENNReal

/-- The term's three provers, before refusal. -/
noncomputable def plainProvers (files : PublicFiles) (parts : Parts files) :
    HonestProvers ((flashProveDescription.F files).withProvers (flashProveDescription.P files)) :=
  ⟨(honestProvers files parts).T, (honestProvers files parts).Lk, (honestProvers files parts).B⟩

/-- **The three statements, at one protocol.** -/
structure TheThreeIOPStatements (files : PublicFiles) {parameters : Inst.Model.ScalesAndPolicy}
    (read : readFiles files = .ok parameters) (parts : Parts files)
    (offlineStops linkStops onlineStops : ℝ≥0∞) : Prop where
  sound : SoundAsIOPAtFiles files (filesAt files).fixedMessageProvers
  complete : CompleteOnServedRequests files read (proversAtFiles files read (plainProvers files parts))
  zeroKnowledge : ZeroKnowledgeOnServedRequests files read (plainProvers files parts)
    offlineStops linkStops onlineStops
  servedIsTrue : ∀ index instance_, ServedRequest committerCoinCountLessOne files read index instance_ →
    relationAtFiles files index instance_

end VerifiableInference.Compilation
