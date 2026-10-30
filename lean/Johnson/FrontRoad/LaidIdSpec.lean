-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/LaidIdSpec.lean: the statement of index privacy for a scheme whose only public key
is the 256-bit commitment ID, whose verifier is, by definition, the verifier of Ladder.lean, whose
link prover is the explicit one, and whose other two provers are placeholder provers, which send
fixed messages. Its committer and prover are written for this statement and are not the
description's own. Definitions and statements; the proofs are in Johnson/FrontRoad/LaidId.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
Spec.idLaid: for every b and all public files Z in scope, the scheme laidId has index privacy in the
stronger of the library's two forms (ZKCP.HasStrongIndexPrivacyWith, ZKCP/Defs.lean), over one hash
function, at all weights, for the relation relTaken, with the explicit simulator laidIdSim, which is
given nothing of the weights. The error for an adversary with at most t queries and up to s1
requests is at most boundZ (9 + CT + CL + CB) M (t + 1) N (E2E/ZetaAtCaps.lean). The premises are
that Z is in scope, that E lists each value once, and seven inequalities: four on the numbers M, s1
and ℓ, and three that bound the search limits from above.
Spec.idLaidNumber: at one copy, 256 sampled bits in a leaf's salt, search limits of 2 ^ 40 (a limit
c allows c + 1 attempts) and an enumeration picked by choice, the only premises are that Z is in
scope and s1 ≤ 688127. With these placeholder provers the simulator's error is at most 2 ^ -135 (one
copy, one request, fewer than 2 ^ 64 hash queries). In the statement that is: if 1 ≤ s1, for t + 1 ≤
2 ^ 64. For more requests see Johnson/FrontRoad/LaidNumbers.lean.

  laidId   the scheme. Its committer reads the public digests off the hash function, as the verifier
      of Ladder.lean does (laidId_reads_as_verify, Johnson/FrontRoad/LaidId.lean), commits to the
      matrix of the weights with the honest side laidAt (E2E/LinkLaidPrivacy.lean), asks the hash
      function once more for the commitment ID, and publishes the ID alone. Its prover puts into
      each proof the root, the out-of-domain sample and the first table's proof, which the committer
      made once, and of the M + 1 link entries the one at the drawn place. It is frontId
      (Johnson/FrontRoad/FrontId.lean) at the description flashProveDescription.reBound b, the family homeT b Z and
      that honest side.
  laidIdSim   the simulator, an explicit term (frontSimK, Johnson/FrontRoad/FrontK.lean).
  relTaken s   the relation: at all weights, every request that the library's builder of instances
      accepts with no further tokens (Flat.buildReq, Johnson/Flat/LedgerClaim.lean). Its public
      parameter is the one value of Unit.
  backTok   reads a request's prompt and output tokens back from an instance.
  pickBits   an enumeration of the sampled bits of the link's hashed run, picked by choice.

How it fits. It applies the theorem on index privacy of this folder (threeOfId_of_laws,
Johnson/FrontRoad/IdAlone.lean) to parameters that satisfy its premises
(Johnson/FrontRoad/LaidAll.lean). Not one of the release's goal statements.

Limits.
  Two of the scheme's three provers are placeholder provers, which send fixed messages: the prover
      for the first table and the prover for the sessions. What depends on the weights in the view,
      and is covered by the statement: the commitment ID, the tables' roots and out-of-domain
      samples, the link prover's messages, and the symbols of the tables' encodings at the positions
      that the three hashed runs open, the placeholders' runs among them. What is not there, and so
      is not covered: messages of a prover for the first table or for the sessions that are computed
      from the weights.
  There is no completeness. The verifier of Ladder.lean is not shown to accept any proof of this
      scheme; that it rejects the placeholders' proofs is argued on paper, not proved. Index privacy
      does not read a scheme's verifier, so that laidId has that verifier holds by definition
      (laidId_V, Johnson/FrontRoad/LaidId.lean). The scheme is not the protocol of the release.
  Neither statement says that a proof is produced. Spec.idLaid bounds the search limits from above
      alone, and at small limits a search hardly ever succeeds, so that the proofs hold nothing. For
      limits of 2 ^ 40 - 1 or more see Spec.laidProduced (Johnson/FrontRoad/LaidBesideSpec.lean).
  The settings s are a variable of which nothing is asked. At settings that are not valid the map
      from weights to the committed matrix (backB) sends all weights to one fixed matrix, and the
      type of weights may be empty: the statement is vacuous there. For the settings that are read
      off the stored public files see Spec.idLaidOwn (Johnson/FrontRoad/LaidBesideSpec.lean).
  It is not asked that the description is live at Z (protocolDataWellFormed). Where it is not, the verifier of
      Ladder.lean rejects everything, and the first table's proof and a session's proof open
      nothing. It is live at the two named sets of public files (open_zFull, open_zGap,
      AtFullSide/E2E/AtWrittenFiles.lean, in the side library).
  Spec.idLaid says nothing where its bound is 1 or more, as it is at large CT, CL or CB. It holds at
      every ℓ from 256 up to the length of a leaf's salt. A hashed run of the protocol publishes the
      first 256 bits of a leaf's salt, so above 320 sampled bits (where the salt has 576) the scheme
      counts as sampled what the protocol publishes (see the notes in E2E/ZetaAtCaps.lean).
  No theorem says that two different sets of weights give two different views of laidId.
  The simulator answers every query to the hash function itself; it is held to consistent answers
      alone, has no bound on its running time, and holds enumerations that are picked by choice. It
      is given the largest number N of requests. s1 is a parameter of the simulator and of the
      bound, not of the scheme. It is a term in the public files Z. What Z itself tells is outside
      what is hidden, and Z holds the file of scales, which for a fitted model are made from its
      weights.
  The weights, the environment and the public files are fixed before the hash function is sampled.
      The environment has no access to the hash function of its own. The distance is statistical.
      The honest side's coins are fresh and uniform, where the programs derive theirs from a seed.
      One request per proof: batches, which the programs have, are not covered.
  relTaken holds of requests whose output is not the model's as well. That makes the statement
      stronger, and it is possible only because the sessions' prover is a placeholder. It leaves out
      every request that the builder refuses (an empty prompt or output; a number that is no token
      of the vocabulary; more than 1,025 tokens together; it refuses no other, by buildReq_total,
      Johnson/Flat/BuiltOK.lean), whether or not its output is the model's.
  The committer and the prover are this folder's, not the fields commit and prove of the
      description, which are placeholders at the description that the goals read
      (Johnson/Goal/Description/Honest.lean). The prover's key and the relation are not those of the
      system of Ladder.lean either. The public parameters are: at this description they are the one
      value of Unit there too, by definition: its honest side is the filler `fixedCommitterAndProver`, whose Shown is
      Unit (Johnson/Goal/Tie/DescriptionOfData.lean; `theHonest`, Johnson/Goal/Description/Honest.lean); no
      theorem here states it.
  It is at the built description with the number of the committer's coins set to b Z. Its verifier
      is the built description's by definition (VerifierAndGoals.verify_reBound). That the built description
      is the description where the goals read it is a theorem
      (theDescription_eq, Johnson/Goal/Description/Description.lean) along which this statement is
      not carried.
  The type of forms, the parser and the encoder of typed proofs into forms are variables of which
      nothing is asked. One request per call; one run of the committer; no further tokens. Beyond s1
      requests the bound is the trivial one: it bounds nothing there, and the clause that the
      simulator's answers are consistent still holds.
  Spec.idLaidNumber is at ℓ = 256 because that is at most the length of a leaf's salt at all public
      files in scope. E2E/LinkLaidPrivacy.lean states its number at ℓ = 320, which needs a live
      description; that is another scheme. The bound reads of ℓ only that 256 ≤ ℓ. At ℓ = 256 and a
      salt of 576 bits the public start has 320 zeros, so 64 bits that the protocol samples are
      zeros here. The length of a leaf's salt is 256 + 8 · saltG (E2E/ZetaAtInput.lean), and a
      hashed run publishes its first 256 bits (by inspection, not proved: the head of
      E2E/ZetaAtCaps.lean). So at public files with saltG = 0 the 256 sampled
      bits of Spec.idLaidNumber are the published ones. Where the description is live the salt has
      576 bits, and the 256 sampled bits lie inside the 320 that are not published.
  Two defaults are not reached under the statements. At a request for which no instance is built the
      prover proves the instance x₀ and does not refuse (instOf, Johnson/FrontRoad/Front.lean);
      relTaken holds of no such request. Where a key has no code the commitment ID would be zeros
      (Johnson/FrontRoad/FrontK.lean); at homeT b Z every key has a code (familyLaws_home,
      Johnson/FrontRoad/AtHomeT.lean).
  The statement follows from index privacy of the scheme that publishes its whole key
      (wholeKeyPrivacy, Johnson/WholeKey/Main.lean) at every value of the public reading, by the
      step across that reading, a re-packing of key and proofs, and one more query. What it adds is
      the form of the key, and that the digests are read off the hash function.
-/
import Johnson.FrontRoad.LaidSides
import Johnson.FrontRoad.IdAlone
import Johnson.Prover.At.HomeMore

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (flashProveData homeR homeT backB flashProveDescription allZeroDigest)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-- The relation: at all weights, every request that the library's builder of instances accepts with
no further tokens. The public parameter is the one value of Unit. -/
def relTaken (s : IntegerTransformer.Settings) :
    ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit Unit where
  rel := fun _ x' _ => ∃ x, Flat.buildReq x' [] = some x
  pp := fun _ => ()

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- The prompt and the output tokens of an instance. -/
def backTok (x : (homeR b Z).Instance) : List Token × List Token :=
  tokensOfRequest (show Flat.Req from x).1

variable (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)

/-- An enumeration of the sampled bits of the link's hashed run that lists each value once, picked
by choice (runBits_listed, Johnson/LinkSim/AtHome/CompileLaid.lean). -/
def pickBits : BitsE b Z b₀ M ℓ ℓr capT capL capB :=
  Classical.choose (runBits_listed _ _ _ _ _ _ _ _)

variable (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (i₀ : (homeR b Z).Index)
  (s : IntegerTransformer.Settings) (x₀ : (homeR b Z).Instance) (Form : Type)
  (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) Z Form)
  (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F Z) ((flashProveDescription.reBound b).P Z) → Form)

/-- **The scheme**: frontId at the description flashProveDescription.reBound b, the family homeT b Z, the library's map
from weights to the committed matrix, and the honest side laidAt at every value of the public
reading. -/
def laidId :=
  frontId (flashProveDescription.reBound b) Z allZeroDigest [] (homeT b Z)
    (fun _ => (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side) s (backB b Z s) x₀ Form parse encF

/-- **The simulator.** It is given the one value of Unit. -/
def laidIdSim : ZKCP.Simulator 256 Unit Commitment (List Token × List Token) Form :=
  frontSimK (homeT b Z) x₀ (backTok b Z) (fun id _ => id)
    (fun k π => encF ([], (lowKey k, lowPrf k π)))
    (laidSides b Z b₀ M s1 ℓ ℓr capT capL capB E i₀).sim fun _ => ()

end OnBytes.FrontRoad

namespace OnBytes.FrontRoad
open AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid VerifiableInference
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (homeR flashProveDescription)

/-- Statement only; proved as idLaid in Johnson/FrontRoad/LaidId.lean. For all public files in
scope, if E lists each value once, under the seven inequalities that the head lists, with two
placeholder provers, which send fixed messages, and no completeness: the scheme laidId has index
privacy in the stronger form, at all weights, with the simulator laidIdSim, at the bound boundZ at
one query more for up to s1 requests. -/
def Spec.idLaid : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr CT CL CB : ℕ)
    (capT capL capB : ℕ → ℕ) (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (i₀ : (homeR b Z).Index)
    (s : IntegerTransformer.Settings) (x₀ : (homeR b Z).Instance) (Form : Type)
    (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) Z Form)
    (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F Z) ((flashProveDescription.reBound b).P Z) → Form),
    InScope Z = true → E.OK → M + 1 ≤ 710324 → s1 ≤ 688127 → 256 ≤ ℓ → ℓ ≤ (homeR b Z).compilerParameters.sMT →
    (∀ i, capT i ≤ CT) → (∀ i, capL i ≤ CL) → (∀ i, capB i ≤ CB) →
    ZKCP.HasStrongIndexPrivacyWith (relTaken s)
      (laidId b Z b₀ M ℓ ℓr capT capL capB E s x₀ Form parse encF)
      (laidIdSim b Z b₀ M s1 ℓ ℓr capT capL capB E i₀ x₀ Form encF)
      fun t N => upTo s1 (boundZ (9 + CT + CL + CB) M) (t + 1) N

/-- Statement only; proved as idLaidNumber in Johnson/FrontRoad/LaidId.lean. The same, with the same
two placeholder provers, which send fixed messages, at one copy, 256 sampled bits in a leaf's salt,
search limits of 2 ^ 40 (2 ^ 40 + 1 attempts) and the picked enumeration. The premises are that Z is
in scope and s1 ≤ 688127. With 1 ≤ s1, for one request and t + 1 ≤ 2 ^ 64, the bound is at most
2 ^ -135. -/
def Spec.idLaidNumber : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (b₀ : (homeR b Z).LeafBody) (s1 ℓr : ℕ) (i₀ : (homeR b Z).Index)
    (s : IntegerTransformer.Settings) (x₀ : (homeR b Z).Instance) (Form : Type)
    (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) Z Form)
    (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F Z) ((flashProveDescription.reBound b).P Z) → Form),
    InScope Z = true → s1 ≤ 688127 →
    ZKCP.HasStrongIndexPrivacyWith (relTaken s)
        (laidId b Z b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
          (pickBits b Z b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40) s x₀ Form
          parse encF)
        (laidIdSim b Z b₀ 0 s1 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
          (pickBits b Z b₀ 0 256 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40) i₀ x₀ Form
          encF)
        (fun t N => upTo s1 (boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (t + 1) N) ∧
      (1 ≤ s1 → ∀ t, t + 1 ≤ 2 ^ 64 →
        upTo s1 (boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (t + 1) 1 ≤ (2⁻¹ : ℝ≥0∞) ^ 135)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.relTaken
#print axioms OnBytes.FrontRoad.laidId
#print axioms OnBytes.FrontRoad.laidIdSim
#print axioms OnBytes.FrontRoad.Spec.idLaid
#print axioms OnBytes.FrontRoad.Spec.idLaidNumber
