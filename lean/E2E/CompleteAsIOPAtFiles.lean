-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPAtFiles.lean: the protocols of the public files Z, as completeness as an IOP takes
them. Definitions, and one example by rfl; no theorem.

  workAtFiles Z     the work bits of the three protocols at Z, as the verifier's wires declare them.
  copyNumberAtFiles Z   the test that a request's messages hold a copy's number.
  completenessTarget   this statement's error, 2⁻⁴¹.
  ServedRequest     the relation: the requests that the model serves.
  CompleteOnServedRequests Z hr Hs   the provers Hs are complete as an IOP there.

protocolAtFiles Z is the object from which verify is compiled: at every digest and further reading, the object in
the input of VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription is (filesAt Z).withProvers (filesAt Z).fixedMessageProvers
(object_description, E2E/DescriptionTie.lean), and the example below says that protocolAtFiles Z is that term.
Its own three provers are placeholders that no verifier reads; a prover stands beside them.

Three relations nest: ServedRequest ⊆ yesAt (servedRequest_isTrue) ⊆ RyesZ Z (below_yesAt,
Johnson/FrontRoad/FromDebts.lean). The statement stands at the smallest: the requests on which the
model's result is their output. Soundness concludes at the largest: the object's relation. What the
smallest leaves out: outputs that the files' policy accepts and that are not the model's own.

The wire is read here at the written pair (allZeroDigest, []): wiring_any (E2E/BridgePremWLink.lean) carries
it to every digest and further reading, so to every value of the public reading. The test on the
copy's number is written without the compiler's letters: num_letters (E2E/BridgeJoinAtFiles.lean)
says that the compiled verifier's test is that one.
-/
import Johnson.Prover.All.CompleteAsIOPForTheCompiler
import Johnson.Goal.Conditions.BindsAtThe
import E2E.BridgePremWLink
import E2E.BridgeJoinAtFiles
import E2E.DescriptionTie
import Johnson.Goal.Conditions.HomeServed
import VerifiableInference.RequestResult

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open VerifiableInference (ModelWeights RequestForm Token requestResult)
open VerifierAndGoals (PublicFiles readFiles settingsOfRead)
open FlashProve (backB allZeroDigest committerCoinCountLessOne homeR)
open OnBytes.Prover (partsWorkOfWire)
open VerifiableInference.Compilation (CompleteIOP HonestProvers)

example (Z : PublicFiles) : protocolAtFiles Z = (filesAt Z).withProvers (filesAt Z).fixedMessageProvers := rfl

/-- **This statement's error**: 2⁻⁴¹. The target is 2⁻⁴⁰, VerifierAndGoals.completenessErrorBound, for the whole statement at
verify; this statement takes half of it. The other half is room for what only
the compiled prover adds: searches for a nonce that run out, and the parser. What is proved on the
way at a larger error is a step, not this statement. -/
def completenessTarget : ℝ≥0∞ := VerifierAndGoals.completenessErrorBound / 2

/-- The work bits of the three parts at the public files Z. -/
abbrev workAtFiles (Z : PublicFiles) : PartsWork (protocolAtFiles Z) :=
  partsWorkOfWire (L := protocolAtFiles Z) (aT := (filesAt Z).annT) (aL := (filesAt Z).annL)
    (lettersZ Z allZeroDigest []).W

/-- Where a request's plain messages hold the copy's number, at Z: the number in the plain part of
its front round. -/
abbrev copyNumberAtFiles (Z : PublicFiles) : ℕ → Plains (protocolAtFiles Z).onlineBatch.loc.shape → Bool :=
  fun k π => decide (((chainsZ Z).plF π).copy = k)

/-- **A served request**: at the index of some weights, a prompt and output tokens make a request,
the model's result on that request is these output tokens, and the instance is what the verifier's
builder makes of them. i: an index. x: an instance. b: a number that the type of an index names and
the relation does not read. -/
def ServedRequest (b : PublicFiles → ℕ) (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (i : (homeR b Z).Index) (x : (homeR b Z).Instance) : Prop :=
  ∃ (w : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
    i = backB b Z (settingsOfRead pp) w ∧
    RequestForm (settingsOfRead pp) prompt output ∧
    requestResult (settingsOfRead pp) w prompt output = some output ∧
    (homeR b Z).buildInstance (prompt, output) [] = some x

/-- **The provers Hs are complete as an IOP at Z**: on the served requests, at this statement's
error. -/
def CompleteOnServedRequests (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (Hs : HonestProvers (protocolAtFiles Z)) : Prop :=
  CompleteIOP (protocolAtFiles Z) Hs (workAtFiles Z) (copyNumberAtFiles Z) (ServedRequest committerCoinCountLessOne Z hr)
    completenessTarget

end AtPublicFiles.AtFiles
