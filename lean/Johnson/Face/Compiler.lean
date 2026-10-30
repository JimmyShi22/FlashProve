-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/Compiler.lean: the compiler: from a protocol, an argument system.

 1. compile is our Commit-and-Prove variant of the BCS transformation (Ben-Sasson, Chiesa, Spooner,
    "Interactive Oracle Proofs", ePrint 2016/116): from a protocol, an argument system.
 2. Each oracle string goes under a salted hash tree, challenges run along a Fiat-Shamir chain, and
    a nonce stands where a round has proof of work: in Lean verifyAtKeyRoot, commitW and proveW.
 3. It must hash as the released programs do, and it is the compiler of which soundness is proved.
 4. A table is an encoding under a hash tree, with its out-of-domain sample; a copy is a further one.
 5. The committer makes the first table with its offline proof, and each copy with its link proof.
 6. The commitment has 256 bits: the hash of the first table's root and out-of-domain sample, with
    the part of the public reading that the key's code tells.
 7. The prover keeps no state: it runs the committer again, then proves one request on one copy,
    drawn at random, by the online proof; at a request that builds no instance it runs at the fallback
    instance.
 8. The verifier: a test on the public files, the parser, two public readings, the compiled verifier.
 9. Two readings and a scope test are the shape of the verifier of the soundness theorem, so that
    compile_verify holds by definition: compile's verifier is the one of which soundness is proved.
10. How a try is counted: an answer of a Fiat-Shamir oracle has many hash blocks, and a search for a
    nonce asks the first block alone and the others only if a test on that block says so, so a failed
    try costs one hash query. Where the test lets through all that a run reads (FirstBlockFits), the
    committer and the prover have the same law of their results at every hash function
    (slot_commit_same, slot_prove_same); which blocks they asked differs.
-/
import Johnson.Face.Protocol
import VerifiableInference.OfArgument
import Ladder
import Johnson.Flat.InnerInputOfThreeProtocols
import Johnson.Top.InnerCompiledVerifierByPublicReading
import Johnson.WholeKey.Premises
import Johnson.FrontRoad.Slot
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestFront
import E2E.BridgeCoins
import ZKCP.CoinsFirstArg

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Compilation
open Rom ZKCP _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles OnBytes.WholeKey RandomizedAlgorithm
open OnBytes.FrontRoad OnBytes.Prover OnBytes.PublicAt
open AtPublicFiles.Bridge (pickAll winR winK winJ)

variable {Index Instance : Type}

/-! ## 1. What the compiler takes -/

/-- A proof as the compiled verifier reads it: further tokens, a key and a proof. -/
abbrev TypedProof (protocol : HolographicProtocol Index Instance)
    (offlineRoundMarks : RoundSplits protocol.offline.shape) (linkRoundMarks : RoundSplits protocol.link.shape) :
    Type :=
  List Token × (KeyRoot 256 protocol × OfflineLinkOnlineProof 256 protocol offlineRoundMarks linkRoundMarks)

/-- How a protocol is laid into one hash function. -/
structure HashLayout (protocol : HolographicProtocol Index Instance)
    (offlineRoundMarks : RoundSplits protocol.offline.shape)
    (linkRoundMarks : RoundSplits protocol.link.shape) where
  /-- What a leaf of a hash tree may hold beside a symbol. -/
  LeafBody : Type
  /-- How rounds and openings are laid into hash queries. -/
  queryLayout : QueryLayout 256 (typedOracleCarrier protocol LeafBody offlineRoundMarks linkRoundMarks)
  /-- The two nested queries that give a table's out-of-domain seed, and the stored copy's number. -/
  seedQueries : OutOfDomainSampleQueryLayout 256 queryLayout.K protocol LeafBody offlineRoundMarks linkRoundMarks
  /-- How out-of-domain answers are written as a list of digests. -/
  answerCode : protocol.OutOfDomainAnswer → List (Dig 256)
  /-- A fixed out-of-domain sample: it fills the two places for one in a session's first query. -/
  fixedSample : protocol.Rec
  /-- The compiler's numbers. -/
  compilerParameters : Params
  /-- All typed oracles, coded into the one hash function. -/
  oracleCoding :
    OracleCoding (typedOracleFamily 256 queryLayout.K (typedOracleCarrier protocol LeafBody offlineRoundMarks linkRoundMarks)) 256
  /-- The code of a key: the hash function's answer at it is the commitment. -/
  keyCode : KeyRoot 256 protocol → Option ZKCP.Str
  /-- The instance of a prompt with output tokens, and further tokens from the proof. -/
  buildInstance : List Token × List Token → List Token → Option Instance

/-- A layout with the six seats of the library's InnerCompilerInput that no verifier reads. -/
structure HashLayoutWithProverFields (protocol : HolographicProtocol Index Instance)
    (offlineRoundMarks : RoundSplits protocol.offline.shape)
    (linkRoundMarks : RoundSplits protocol.link.shape) extends
    HashLayout protocol offlineRoundMarks linkRoundMarks where
  nextToken : Index → List Token → Option Token
  ProverKey : Type
  commit : Index → OComp (typedOracleFamily 256 queryLayout.K
    (typedOracleCarrier protocol LeafBody offlineRoundMarks linkRoundMarks)) (KeyRoot 256 protocol × ProverKey)
  prove : ProverKey → (batch : List (Instance × Unit)) → OComp (typedOracleFamily 256 queryLayout.K
    (typedOracleCarrier protocol LeafBody offlineRoundMarks linkRoundMarks))
    (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 protocol offlineRoundMarks linkRoundMarks) batch)
  coinBound : ℕ
  fallbackProof : KeyRoot 256 protocol × OfflineLinkOnlineProof 256 protocol offlineRoundMarks linkRoundMarks

/-- A layout as the library's InnerCompilerInput. -/
def HashLayoutWithProverFields.input {protocol : HolographicProtocol Index Instance}
    {offlineRoundMarks : RoundSplits protocol.offline.shape} {linkRoundMarks : RoundSplits protocol.link.shape}
    (layout : HashLayoutWithProverFields protocol offlineRoundMarks linkRoundMarks) : InnerCompilerInput where
  Index := Index
  Instance := Instance
  protocol := protocol
  LeafBody := layout.LeafBody
  offlineRoundSplits := offlineRoundMarks
  linkRoundSplits := linkRoundMarks
  queryLayout := layout.queryLayout
  seedQueries := layout.seedQueries
  answerCode := layout.answerCode
  fixedSample := layout.fixedSample
  compilerParameters := layout.compilerParameters
  oracleCoding := layout.oracleCoding
  keyCode := layout.keyCode
  buildInstance := layout.buildInstance
  nextToken := layout.nextToken
  ProverKey := layout.ProverKey
  commit := layout.commit
  prove := layout.prove
  coinBound := layout.coinBound
  fallbackProof := layout.fallbackProof

/-- The public side of what is compiled, at one set of public files. -/
structure PublicSide where
  /-- What is committed, as the protocol sees it. -/
  Index : Type
  /-- What a session proves. -/
  Instance : Type
  /-- The protocol. -/
  protocol : HolographicProtocol Index Instance
  /-- Which rounds of the offline protocol are shared by a batch. -/
  offlineRoundSplits : RoundSplits protocol.offline.shape
  /-- Which rounds of the link protocol are shared by a batch. -/
  linkRoundSplits : RoundSplits protocol.link.shape
  /-- Whether the verifier takes these public files at all. -/
  filesInScope : Bool
  /-- The first public reading: the digest of the public files, asked of the hash function. -/
  filesDigest : DeterministicAlgorithm Digest
  /-- What the second public reading returns. -/
  Further : Type
  /-- The second public reading. -/
  furtherReading : Digest → DeterministicAlgorithm Further
  /-- The layout in force, as a function of what the two readings returned. -/
  layoutAt : Digest → Further → HashLayoutWithProverFields protocol offlineRoundSplits linkRoundSplits
  /-- The model. -/
  model : Model
  /-- From the weights, what the protocol commits to. -/
  indexOf : model.Weights → Index

/-- The library's family of layouts in one value of the public reading. -/
abbrev LayoutFamily := LayoutsByPublicReading

/-- The layouts as the committer and the prover read them, and that they are the verifier's. -/
structure CompilerWiring (side : PublicSide) where
  /-- Values of the two readings at which the family is typed. -/
  baseDigest : Digest
  /-- The same for the second reading. -/
  baseFurther : side.Further
  /-- The layouts as one family in one value of the public reading. -/
  family : LayoutFamily (side.layoutAt baseDigest baseFurther).input
  /-- Where the two readings' values stand in the family's. -/
  pair : Digest → side.Further → family.D
  /-- The verifier's layouts and the family are one wiring. -/
  agree : ∀ digest further, family.at (pair digest further) = (side.layoutAt digest further).input
  /-- The instance that stands where a request builds none. -/
  fallbackInstance : side.Instance

/-- How a proof is written down. -/
structure ProofFormat (protocol : HolographicProtocol Index Instance)
    (offlineRoundMarks : RoundSplits protocol.offline.shape)
    (linkRoundMarks : RoundSplits protocol.link.shape) where
  /-- A written proof. -/
  Form : Type
  /-- The parser, part of the verifier: from any form it returns some typed proof. -/
  parse : List Token → List Token → Form →
    DeterministicAlgorithm (TypedProof protocol offlineRoundMarks linkRoundMarks)
  /-- The writer, part of the honest prover. -/
  write : TypedProof protocol offlineRoundMarks linkRoundMarks → Form

/-- The three provers as the library's type of them. -/
def HonestProvers.toRecs {protocol : HolographicProtocol Index Instance}
    (provers : HonestProvers protocol) : ThreeProvers protocol :=
  ⟨provers.offlineProver, provers.linkProver, provers.onlineProver⟩

variable {L : HolographicProtocol Index Instance} {offlineRoundMarks : RoundSplits L.offline.shape}
  {linkRoundMarks : RoundSplits L.link.shape}

/-- **What the honest side chooses beside its three provers.** The verifier reads none of it.
RunValues: strings that a prover's coins fix and that the prover also sends in the clear; the public
starts of a compiled run's salts are made of them. AT PLAIN STARTS (RunValues := Unit) the starts
are constants. -/
structure CompiledSettings (layout : HashLayout L offlineRoundMarks linkRoundMarks)
    (provers : HonestProvers L) where
  leafFiller : layout.LeafBody
  /-- in round i the search for a nonce may try searchLimit i + 1 nonces -/
  searchLimitOffline : ℕ → ℕ
  searchLimitLink : ℕ → ℕ
  searchLimitOnline : ℕ → ℕ
  /-- there are furtherCopies + 1 copies -/
  furtherCopies : ℕ
  /-- the number of the copy at a place of the key's list: public -/
  copyNumber : ℕ → ℕ
  RunValues : Type
  wellFormed : RunValues → Prop
  runValuesOffline : provers.offlineProver.Coin → RunValues
  runValuesLink : provers.linkProver.Coin → RunValues
  runValuesOnline : provers.onlineProver.Coin → RunValues
  readOffline : Plains L.offline.shape → RunValues
  readLink : Plains L.link.shape → RunValues
  readOnline : Plains L.onlineBatch.loc.shape → RunValues
  saltStartOffline : RunValues → ℕ → Bool → Bits → Bits
  saltStartLink : RunValues → ℕ → Bool → Bits → Bits
  saltStartOnline : RunValues → ℕ → Bool → Bits → Bits
  slotTail : ℕ → Bits
  windowFiller : Bits
  /-- the public start of a table's salt, the free bits of a salt, paddings and slots -/
  coinNumbers : CoinNums layout.LeafBody

open Classical in
/-- **The compiler's honest side**: the provers as they are; every finite type of coins enumerated
whole; salts and run coins with public starts and uniform free bits. The compiled prover withholds
on the provers' two abort sets, decided by the excluded middle. -/
def honestSide (layout : HashLayout L offlineRoundMarks linkRoundMarks)
    (provers : HonestProvers L) (s : CompiledSettings layout provers) :
    AtRecs 256 L layout.LeafBody offlineRoundMarks linkRoundMarks where
  Hs := provers.toRecs
  dc := ⟨fun _ _ _ => propDecidable _, fun _ _ _ => propDecidable _, fun _ _ _ => propDecidable _⟩
  b₀ := s.leafFiller
  capT := s.searchLimitOffline
  capL := s.searchLimitLink
  capB := s.searchLimitOnline
  M := s.furtherCopies
  nm := s.copyNumber
  RV := s.RunValues
  okV := s.wellFormed
  rvT := s.runValuesOffline
  rvL := s.runValuesLink
  rvB := s.runValuesOnline
  startT := s.saltStartOffline
  startL := s.saltStartLink
  startB := s.saltStartOnline
  pvT := s.readOffline
  pvL := s.readLink
  pvB := s.readOnline
  rtail := s.slotTail
  nR := winR (L := L)
  nK := winK layout.queryLayout
  nJ := winJ layout.queryLayout
  fill := s.windowFiller
  ri := pickAll L.EncodingRandomness
  sl := saltsPre s.coinNumbers.pre₀ (2 ^ layout.queryLayout.depth) s.coinNumbers.ℓ (pickAll _)
  kT := pickAll provers.offlineProver.Coin
  kL := pickAll provers.linkProver.Coin
  kB := pickAll provers.onlineProver.Coin
  coT := coinsPre (winR (L := L)) (winK layout.queryLayout) (winJ layout.queryLayout) layout.compilerParameters.sFS
    s.coinNumbers.ℓ s.coinNumbers.ℓr
    layout.queryLayout.depthReqT s.coinNumbers.padT s.coinNumbers.slotT s.windowFiller (pickAll _)
  coL := coinsPre (winR (L := L)) (winK layout.queryLayout) (winJ layout.queryLayout) layout.compilerParameters.sFS
    s.coinNumbers.ℓ s.coinNumbers.ℓr
    layout.queryLayout.depthReqL s.coinNumbers.padL s.coinNumbers.slotL s.windowFiller (pickAll _)
  coB := coinsPre (winR (L := L)) (winK layout.queryLayout) (winJ layout.queryLayout) layout.compilerParameters.sFS
    s.coinNumbers.ℓ s.coinNumbers.ℓr
    layout.queryLayout.depthReq s.coinNumbers.padB s.coinNumbers.slotB s.windowFiller (pickAll _)

/-- **THE COMPILATION, over typed random oracles: committer, prover and verifier out of (protocol,
provers, wiring, settings).** It is the library's scheme with the whole key published, argW. Its
verifier is the compiled verifier, which reads no prover and no setting. -/
def compileOverTypedOracles (layout : HashLayout L offlineRoundMarks linkRoundMarks)
    (provers : HonestProvers L) (s : CompiledSettings layout provers) :
    ZKCP.Gen.Arg (typedOracleFamily 256 layout.queryLayout.K (typedOracleCarrier L layout.LeafBody offlineRoundMarks
                   linkRoundMarks)) Index Instance Unit
      (FullKey 256 L offlineRoundMarks linkRoundMarks) (Isk 256 L layout.LeafBody
           offlineRoundMarks linkRoundMarks)
      (RequestProof 256 L) :=
  argW layout.queryLayout layout.seedQueries layout.answerCode layout.fixedSample layout.compilerParameters (honestSide layout provers
    s).side

/-- The layout at a value of the public reading: the seed's queries and the answers' code move with
the reading, the layout of queries does not. -/
@[reducible] def CompilerWiring.layoutAtReading {side : PublicSide} (wiring : CompilerWiring side)
    (reading : wiring.family.D) :
    HashLayout side.protocol side.offlineRoundSplits side.linkRoundSplits :=
  { (side.layoutAt wiring.baseDigest wiring.baseFurther).toHashLayout with
    seedQueries := wiring.family.Sd reading
    answerCode := wiring.family.cA reading }

/-- **What compile takes.** -/
structure Compilable where
  /-- The protocol, its layouts, the readings, the model. -/
  publicSide : PublicSide
  /-- The layouts as the committer and the prover read them. -/
  wiring : CompilerWiring publicSide
  /-- The honest provers. -/
  provers : HonestProvers publicSide.protocol
  /-- What the honest side chooses beside its provers, at each value of the public reading. -/
  settings : (reading : wiring.family.D) → CompiledSettings (wiring.layoutAtReading reading) provers
  /-- The test on an answer's first hash block by which a search for a nonce decides whether to ask
  the other blocks: a failed try costs one call. -/
  firstBlockTest : (reading : wiring.family.D) → Rom.More (typedOracleFamily 256
    (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.queryLayout.K
    (typedOracleCarrier (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.protocol
      (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.LeafBody
      (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.offlineRoundSplits
      (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.linkRoundSplits)) 256
  /-- The honest committer samples one number from 0 to this. -/
  coinBound : ℕ
  /-- The proof format. -/
  format : ProofFormat publicSide.protocol publicSide.offlineRoundSplits publicSide.linkRoundSplits

/-! ## 2. The compiler -/

/-- The four parts of an argument system that its verifier does not read. -/
structure CompiledSide (Weights Form : Type) where
  Randomness : Type
  sample : RandomizedAlgorithm Randomness
  commit : Weights → Randomness → DeterministicAlgorithm Commitment
  prove : Weights → Randomness → List Token → List Token → RandomizedAlgorithm Form

/-- The argument system at a model, a side and a verifier. It has no public parameters. -/
def systemOf {Weights Form : Type} (nextToken : Weights → List Token → Option Token)
    (side : CompiledSide Weights Form)
    (verifier : Commitment → List Token → List Token → Form → DeterministicAlgorithm Bool) :
    ArgumentSystem where
  Weights := Weights
  PublicParameters := Unit
  publicParameters := fun _ => ()
  CommitmentRandomness := side.Randomness
  Proof := Form
  nextToken := nextToken
  sampleCommitmentRandomness := side.sample
  commit := side.commit
  prove := side.prove
  verify := verifier

/-- **The compiled verifier.** It reads the public side and the parser alone. -/
def compiledVerifier (side : PublicSide) {Form : Type}
    (parse : List Token → List Token → Form → DeterministicAlgorithm
      (TypedProof side.protocol side.offlineRoundSplits side.linkRoundSplits))
    (commitment : Commitment) (prompt output : List Token) (form : Form) :
    DeterministicAlgorithm Bool :=
  if side.filesInScope then
    VerifierAndGoals.andThen (parse prompt output form) fun proof =>
      VerifierAndGoals.andThen side.filesDigest fun digest =>
        VerifierAndGoals.andThen (side.furtherReading digest) fun further =>
          innerCompiledVerifier (side.layoutAt digest further).input commitment prompt output proof
  else .done false

variable (input : Compilable)

/-- The scheme: the committer and prover over the family. What is published is the 256-bit
commitment; a proof holds the first table's root and out-of-domain sample, what was made once, and
the session's proof. -/
def compiledScheme : ZKCP.Arg 256 input.publicSide.model.Weights (List Token × List Token) Unit
    Commitment
    (FullKey 256 input.publicSide.protocol input.publicSide.offlineRoundSplits
        input.publicSide.linkRoundSplits ×
      (input.wiring.family.D × Isk 256 input.publicSide.protocol
        (input.publicSide.layoutAt input.wiring.baseDigest input.wiring.baseFurther).LeafBody
        input.publicSide.offlineRoundSplits input.publicSide.linkRoundSplits))
    input.format.Form :=
  committerAndProverOverOneHash input.wiring.family
    (fun reading => (honestSide (input.wiring.layoutAtReading reading) input.provers
      (input.settings reading)).side)
    input.firstBlockTest input.publicSide.indexOf input.wiring.fallbackInstance (fun id _ => id)
    (fun key proof => input.format.write ([], (lowKey key, lowPrf key proof)))
    fun commitment request form =>
      (compiledVerifier input.publicSide input.format.parse commitment request.1 request.2
        form).toRandomized.toUpload

/-- The committer samples one number and runs the scheme's committer at it; the prover is given the
weights and that number. -/
def compiledSide : CompiledSide input.publicSide.model.Weights input.format.Form where
  Randomness := Fin (input.coinBound + 1)
  sample := .sample input.coinBound fun coins => .done coins
  commit := fun weights coins => deterministicOf
    ((((compiledScheme input).C weights).withCoins coins.val).mapO Prod.fst)
  prove := fun weights coins prompt output => ofUpload
    (((compiledScheme input).coinsFirst input.coinBound).P (weights, coins) (prompt, output) ())

/-- **The compiler.** -/
def compile : ArgumentSystem :=
  systemOf input.publicSide.model.nextToken (compiledSide input)
    (compiledVerifier input.publicSide input.format.parse)

/-! ## 3. A description, read as a public side -/

open VerifierAndGoals
open IntegerTransformer (Settings)
open scoped ENNReal

/-- The integer model at given settings. -/
def integerModel (settings : Settings) : Model where
  Weights := ModelWeights settings
  nextToken := modelNextToken settings

/-- The letters of a description as a layout: field by field. -/
def layoutOf (D : Description) (Z : PublicFiles) (c : Digest) (m : D.More) :
    HashLayoutWithProverFields ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL where
  LeafBody := (D.T Z c m).Bd
  queryLayout := (D.T Z c m).W
  seedQueries := (D.T Z c m).Sd
  answerCode := (D.T Z c m).cA
  fixedSample := (D.T Z c m).r₀
  compilerParameters := (D.T Z c m).p
  oracleCoding := (D.T Z c m).m
  keyCode := (D.T Z c m).enc
  buildInstance := (D.T Z c m).build
  nextToken := (D.T Z c m).nextToken
  ProverKey := (D.T Z c m).ISK
  commit := (D.T Z c m).commit
  prove := (D.T Z c m).prove
  coinBound := (D.T Z c m).bound
  fallbackProof := (D.T Z c m).π₀

/-- A description at public files Z and settings s, with the map from weights to indices. -/
def ofDescription (D : Description) (Z : PublicFiles) (s : Settings) (idx : ModelWeights s → (D.C Z).I) :
    PublicSide where
  Index := (D.C Z).I
  Instance := (D.C Z).X
  protocol := (D.F Z).withProvers (D.P Z)
  offlineRoundSplits := (D.F Z).annT
  linkRoundSplits := (D.F Z).annL
  filesInScope := InScope Z
  filesDigest := readConfig Z
  Further := D.More
  furtherReading := D.readMore Z
  layoutAt := layoutOf D Z
  model := integerModel s
  indexOf := idx

/-- A family over a description's input that agrees with it, with an instance. -/
def wiringOf (D : Description) (Z : PublicFiles) (s : Settings) (idx : ModelWeights s → (D.C Z).I)
    (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D)
    (agree : ∀ c m, T.at (pair c m) = D.input Z c m) (x₀ : (D.C Z).X) :
    CompilerWiring (ofDescription D Z s idx) where
  baseDigest := c₀
  baseFurther := m₀
  family := T
  pair := pair
  agree := agree
  fallbackInstance := x₀

/-- A parser of a description, with a writer, as a proof format. -/
def formatOf (D : Description) (Z : PublicFiles) (Form : Type) (parse : Parser D Z Form)
    (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form) :
    ProofFormat ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL :=
  ⟨Form, parse, write⟩

section Ties

variable (D : Description) (Z : PublicFiles) (s : Settings) (idx : ModelWeights s → (D.C Z).I) (c₀ : Digest)
  (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D)
  (agree : ∀ c m, T.at (pair c m) = D.input Z c m) (x₀ : (D.C Z).X)
  (provers : HonestProvers ((D.F Z).withProvers (D.P Z)))
  (settings : (reading : T.D) →
    CompiledSettings ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers)
  (firstBlockTest : (reading : T.D) → Rom.More (typedOracleFamily 256 (D.input Z c₀ m₀).queryLayout.K
    (typedOracleCarrier (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)) 256)
  (coinBound : ℕ) (Form : Type) (parse : Parser D Z Form)
  (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form)

/-- What compile takes, at a description. -/
abbrev atDescription : Compilable :=
  ⟨ofDescription D Z s idx, wiringOf D Z s idx c₀ m₀ T pair agree x₀, provers, settings,
    firstBlockTest, coinBound, formatOf D Z Form parse write⟩

/-- A layout of a description is the description's input. -/
theorem layoutOf_input (c : Digest) (m : D.More) : (layoutOf D Z c m).input = D.input Z c m := rfl

/-- The compiled verifier of a description's public side is VerifierAndGoals.verify. -/
theorem compiledVerifier_eq_verify :
    compiledVerifier (ofDescription D Z s idx) parse = verify D Z parse := rfl

/-- **compile's verifier is VerifierAndGoals.verify**, at every description. -/
theorem compile_verify :
    (compile (atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest
      coinBound Form parse write)).verify = verify D Z parse := rfl

/-- **Sound reads no honest part**: of compile it is Sound of VerifierAndGoals's system, whatever its prover. -/
theorem compile_sound_iff
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (ε : ℕ → ℝ≥0∞) :
    Sound (compile (atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest
        coinBound Form parse write)) ε ↔
      Sound (system D Z s Form prove parse) ε :=
  Iff.rfl

/-- An argument system is itself with its verifier written anew, if the two are one. -/
theorem withVerify (system : ArgumentSystem)
    (verifier : Commitment → List Token → List Token → system.Proof → DeterministicAlgorithm Bool)
    (same : system.verify = verifier) : { system with verify := verifier } = system := by
  subst same
  rfl

/-- **compile is slotSystem with committer and prover by the early exit of the nonce search**
(Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTest.lean), on which the theorems on hiding and completeness stand. -/
theorem compile_eq_slotSystemF :
    compile (atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound
      Form parse write) =
      slotSystemF D Z c₀ m₀ T (fun reading => (honestSide
        ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers
        (settings reading)).side) firstBlockTest s idx x₀ Form parse write coinBound :=
  withVerify (slotSystemF D Z c₀ m₀ T (fun reading => (honestSide
      ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers
      (settings reading)).side) firstBlockTest s idx x₀ Form parse write coinBound) (verify D Z parse)
    (slotF_verify D Z c₀ m₀ T (fun reading => (honestSide
      ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers
      (settings reading)).side) firstBlockTest s idx x₀ Form parse write coinBound)

end Ties

end VerifiableInference.Compilation
