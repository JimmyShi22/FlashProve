-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/LaidBesideSpec.lean: two statements beside Spec.idLaid
(Johnson/FrontRoad/LaidIdSpec.lean): the proofs of the scheme laidId are produced, and the statement
at the stored full-size public files' own settings, where different weights give different committed
matrices. Definitions and statements; the proofs are in Johnson/FrontRoad/LaidBeside.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
Spec.laidProduced: for every b and all public files Z in scope, if each proof-of-work search may
make at least 2 ^ 40 attempts, then in one run of laidId's committer and one run of its prover, for
a request that relTaken holds of, all proof strings are present except with probability at most
(M + 2) · 71 · 2 ^ -256: the proof on the first table, all M + 1 link proofs, which the explicit
link prover makes, and the session's proof. The probability is over the hash function and the coins.
Spec.idLaidOwn: there are parameters pp that the reader returns at the stored full-size public files
storedPublicFiles, and at the settings s := settingsOfRead pp: the scheme laidId has index privacy as in
Spec.idLaidFull (Johnson/FrontRoad/LaidIdFull.lean), with two placeholder provers, which send fixed
messages; the map from weights to the committed matrix is one-to-one; and there are two different
sets of weights.

How Spec.laidProduced is stated. A form need not show what it holds, since the encoder of typed
proofs into forms is a variable. So the statement is about the whole key and the typed proof before
they are put into their final form. It is written as a completeness error: laidOpen is the scheme
with laidId's committer and prover that shows the pair (commitment ID, whole key) and the typed
proof, with the test allThere in the verifier's place. Its "verifier" asks no oracle, checks nothing
about the instance, and returns whether all proof strings are present. So "laidOpen has completeness
error at most α" says that the test fails with probability at most α, and it says nothing about
what a verifier of the protocol accepts. That laidId's committer and prover are laidOpen's, followed
by the maps to the commitment ID and to a form, is laidId_C_of_open and laidId_P_of_open
(Johnson/FrontRoad/LaidBeside.lean).

  allThere n k π   the test: FullTo n (E2E/StringsAllLinks.lean) of the key k and the proof π, as a
      Boolean value by classical decidability.
  laidOpen   openArg (Johnson/FrontRoad/TestInPlace.lean) at the family homeT b Z, the honest side
      laidAt and the test allThere (M + 1).

How it fits. Index privacy also holds of a scheme whose searches never succeed and whose proofs
therefore hold nothing. Spec.laidProduced rules that out for laidId at search limits of 2 ^ 40 - 1
or more. Spec.idLaidOwn rules out that all weights are sent to one matrix, which happens at settings
that are not valid. Not among the release's goal statements.

Limits.
  "Present" is not "accepted". Two of the three provers are placeholder provers, which send fixed
      messages; their proofs are present and no verifier is shown to accept them. There is no
      completeness of laidId.
  Spec.laidProduced is about one run of the committer and one request, both fixed before the hash
      function is sampled.
  That a link proof which is present depends on the weights is not said here. For the link prover's
      messages before hashing see E2E/LinkLaidTwoViews.lean.
  Neither statement asks that the description is live at Z (protocolDataWellFormed). At storedPublicFiles it is
      (AtPublicFiles.AtWritten.open_zFull, AtFullSide/E2E/AtWrittenFiles.lean, in the side library). Where it
      is not, the first table's proof and a session's proof open nothing.
  All limits of Johnson/FrontRoad/LaidIdSpec.lean.
-/
import Johnson.FrontRoad.LaidIdFull
import Johnson.FrontRoad.TestInPlace

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifierAndGoals (PublicFiles InScope storedPublicFiles)
open FlashProve (homeR homeT backB flashProveDescription allZeroDigest)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows VerifierAndGoals.storedPublicFiles

/-- The test: the first table's proof, the link proofs at the first n places, the link proof at the
place that the proof names and the session's proof are all present. -/
def allThere {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (n : ℕ) (k : FullKey lam L aT aL) (π : RequestProof lam L) : Bool :=
  @decide (AtPublicFiles.Shown.FullTo n (k, π)) (Classical.dec _)

variable (b : PublicFiles → ℕ) (Z : PublicFiles) (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (s : IntegerTransformer.Settings) (x₀ : (homeR b Z).Instance)

/-- The scheme with laidId's committer and prover that shows the pair (commitment ID, whole key) and
the typed proof, with the test allThere (M + 1) in the verifier's place. -/
def laidOpen :=
  openArg (homeT b Z) (fun _ => (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side) (allThere (M + 1))
    (backB b Z s) x₀

end OnBytes.FrontRoad

namespace OnBytes.FrontRoad
open AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid VerifiableInference
open VerifierAndGoals (PublicFiles InScope storedPublicFiles)
open FlashProve (homeR backB flashProveDescription)

/-- Statement only; proved as laidProduced in Johnson/FrontRoad/LaidBeside.lean. For all public
files in scope and search limits that allow at least 2 ^ 40 attempts, the honest key and proof of
laidOpen
fail the test "all proof strings are present" with probability at most (M + 2) · 71 · 2 ^ -256. -/
def Spec.laidProduced : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (s : IntegerTransformer.Settings)
    (x₀ : (homeR b Z).Instance),
    InScope Z = true → (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) →
    ZKCP.HasCompletenessError (relTaken s) (laidOpen b Z b₀ M ℓ ℓr capT capL capB E s x₀)
      (((M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256))

/-- Statement only; proved as idLaidOwn in Johnson/FrontRoad/LaidBeside.lean. At the settings that
are read off the stored full-size public files: index privacy of laidId as in Spec.idLaidFull, with
two placeholder provers, which send fixed messages; the map from weights to the committed matrix is
one-to-one; there are two different sets of weights. -/
def Spec.idLaidOwn : Prop :=
  ∃ pp, VerifierAndGoals.readFiles storedPublicFiles = .ok pp ∧
    (∀ (b : PublicFiles → ℕ) (b₀ : (homeR b storedPublicFiles).LeafBody) (ℓr : ℕ) (i₀ : (homeR b storedPublicFiles).Index)
      (x₀ : (homeR b storedPublicFiles).Instance) (Form : Type) (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) storedPublicFiles Form)
      (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F storedPublicFiles) ((flashProveDescription.reBound b).P storedPublicFiles) → Form),
      ZKCP.HasStrongIndexPrivacyWith (relTaken (VerifierAndGoals.settingsOfRead pp))
        (laidId b storedPublicFiles b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
          (pickBits b storedPublicFiles b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40)
          (VerifierAndGoals.settingsOfRead pp) x₀ Form parse encF)
        (laidIdSim b storedPublicFiles b₀ 0 688127 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
          (pickBits b storedPublicFiles b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40) i₀ x₀
          Form encF)
        fun t N => upTo 688127 (boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (t + 1) N) ∧
    (∀ b : PublicFiles → ℕ, Function.Injective (backB b storedPublicFiles (VerifierAndGoals.settingsOfRead pp))) ∧
    ∃ w w' : ModelWeights (VerifierAndGoals.settingsOfRead pp), w ≠ w'

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.allThere
#print axioms OnBytes.FrontRoad.laidOpen
#print axioms OnBytes.FrontRoad.Spec.laidProduced
#print axioms OnBytes.FrontRoad.Spec.idLaidOwn
