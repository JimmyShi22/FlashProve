-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TwoSizes.lean: the input made of the three files' protocols at the two sizes of the
default setting, over the compiled verifier that hashes a file as three chains, and the named
hypotheses that are left there.

Definitions; at each size five structures that part the sixteen named hypotheses (by a definition;
by construction; proved with content; true of a wiring of our own choice; left), the proofs of the
first four, and the theorems. `innerCompilerInputFromDryRunAtFullSize T`, `innerCompilerInputFromDryRunAtSmallSize T : InnerCompilerInput`
(Johnson/Top/InnerCompiledVerifier.lean): the object is `(threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P` | the small twin
(OnBytes/Flat/FilesAt.lean, Object.lean); the key file's marks are the makers' own; the entry file's
are the written link's own (all local); the record's wire is written (`outOfDomainSampleQueryLayoutOfCode`,
Johnson/Flat/SeedTwin.lean: it holds the code of a record), so are the code of its answers (`codeA`,
OnBytes/Flat/RecordCode.lean) and its seed (`recSeedK`, OnBytes/Flat/RecordSeed.lean); the wiring is
written (`wireFullAt`, `wireSmallAt`, Johnson/Flat/WireAt.lean), and the body of a leaf is a string
of bits; every round's error is stated at 2^-128, counted with the round's proof of work: stated,
not proved, of the key file's and the proof file's rounds.

Of the sixteen fields of `CompilerSoundnessConditionsWithMeaning`: one holds by the decoder's definition (`noneColl`). Seven hold
by construction: by unfolding and by lemmas that hold of all data: nothing about this protocol is
used (`keyLocal`, `entryLocal`, `proofLocal`, `keyCoherent`, `entryCoherent`, `proofCoherent`,
`answersLength`: the last is a law of the written code `codeA` too, but of its length alone). Three
are proved with content: a fact about this protocol's own rounds or numbers, or a law of a code that
is written in this library, is used: `entrySound` (under the theorem on codes `BCHKS46At GF GE`),
`seedLaw`, `answersCode` (of a code that is written in this library). One is true of a wiring of our
own choice: `wires` (`AtOurWiringFull` | `AtOurWiringSmall`): it was not proved of the programs'
wiring: the wiring was chosen so that it holds. Four are left, in `RemainingSoundnessConditionsFromDryRunAtFullSize` | `RemainingSoundnessConditionsFromDryRunAtSmallSize`:
`keySound`, `proofSound`, `commitment`, `sound`. 16 = 1 + 7 + 3 + 1 + 4. Hypotheses of the theorems
of this file: these four and the theorem on codes `BCHKS46At GF GE`: five. The four are unproved.
The statement on codes (`BCHKS46At`) is proved, for every field F and every finite field E over it,
in Cb/Bridge/CodeListRSProved.lean (`Cb.Bridge.bchks46At`), from two theorems of ArkLib's, in
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md, L15); this file
does not import it and keeps the hypothesis. Beside these stand the laws that
stand in the types of the letters (`T.m : OracleCoding`, Rom/Family.lean: one to one and onto all bit
strings; `A.mat_cut`), which are counted nowhere. The bound holds the letter `T.εId` and the written
wiring's numbers: no number is evaluated.

Where the samplers and the proof of work are: inside the rounds. All three protocols stand at the
kit `ckP .two` (Run/PlanPull.lean): a round's verifier message is blocks of digests with the test
bits of that round's proof of work; the field elements, positions and matrix entries that the
decision reads are made from the blocks inside the decision. So the number of a round's verifier
messages is a power of two, as `wires` needs; and the error of a round is measured as a fraction
of those messages: it takes in the bias of the sampler and is counted with the proof of work.

Limits: those of Johnson/Top/InnerCompiledVerifier.lean; and: letters: A (the claims), E (how an index is
held, encoded and sampled), G (`FilesParameters`, OnBytes/Flat/FilesAt.lean), P (honest provers); T (the length
of a salt; the seeds' tag, the digests and bits of a table's name, the plain parts of the seeds' two
queries, the test on the stored copy's number; a fixed record, `p : Params`, `bound`, `π₀`, which
the verifier or the system reads; the coding in one hash function; the key's code; the extractor
behind the commitment, its cost and an instance; how an instance is built; the model; the honest
side, of which nothing is asked). No value of them is given, and none is shown to meet the
hypotheses that are left. "at the two sizes" holds of the entry file, the decoder and the depth of
the stored tables alone: `G.k`, `G.c`, `G.block` are letters: the key file's and the proof file's
chains are those of no size. The guards are two tests at each size, the key file's and the proof
file's (together `GuardsPassFull` | `GuardsPassSmall`, Johnson/Flat/WireAt.lean): that they pass is
shown at no G. Where one fails, that file's data are empty and its decision says no at every
instance (`runKFull_false`, `runPFull_false`): its hypothesis on soundness is then true for free (by
reading: no theorem draws it from the two lemmas). Where both fail, all that is left is met by a
hollow value: "the four are met" would by itself be no news. Owed in Lean, at values: that the
guards pass (a test: decidable at a closed G); an inhabitant of the letters `InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize` |
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize` (a coding `T.m` in one hash function among them). Owed outside Lean: that the
programs are wired so (K, the three depths, the wire records, the bodies); that the makers' decision
on a file's views is the verifier program's verdict. All is asked here of every G; at a value of the
planner's type of answers (not asked to be an answer): Johnson/Flat/TwoAtPlan.lean. `proofSound` is
asked here of every G: a depth and rounds that nothing ties to the programs' plan: at a free G with
more than one slot and rounds tuned to 2^-128 it may be false, and the theorem is then empty; a
union bound over the slots cannot reach it. By the design, as read at the programs' source and shown
by no theorem here, the slots' sets of bad messages are one set behind the shared point, and the
plan pays the number of slots at one round alone: the rule that proves the step so takes the second
chain as a batch link with keys, charged its own list of errors (OnBytes/TypedOracleCompiler/Joined/LinkJ.lean:
`sndBKT_of_links`; OnBytes/TypedOracleCompiler/Joined/MidLinks.lean: `proofSound_at_links`); the library's link at
the shared point has the split: the fold's term once, N times the algebraic term (Cb/Ld/LdLinB.lean:
`errPtB`). Its premises are shown of no file. `keySound` pays the factor 2 ^
`G.k.oneTime.binding.logLeaves` at the key file's shared rounds: the written wiring lays the depth
of the key file's request tree as the key's chains' own, by our choice: which depth the programs
have is not said here; no number of it is evaluated here (the program's `Key.fixedOk`,
OnBytes/Key/Fixed.lean, admits 0 alone: not used here). `entrySound` pays the factor 1 at every
depth: its marks are all local. At the small size `proofSound`, the hypothesis on the proof file's
protocol, cannot be met by the small example's protocol at `claimsSmall`
(Johnson/Flat/ClaimsSizes.lean: `claimsAt` at the small example's ten sizes): its program is not
that of the small example's parameter file (the five fixed tables are the library's own), so the
small example's programs prove another program (the head of Johnson/Flat/ClaimsAny.lean, in these
words). It is not expected to be met at `claimsLedger`, `claimsReq` (Johnson/Flat/ClaimsLedger.lean,
ClaimsReq.lean): these speak of requests and an index of the reference sizes (`ppref`: a window of
1024), and the small example's sizes are others (`sizesSmall`, Johnson/Flat/ClaimsSizes.lean: a
window of 64). Both by reading: no theorem. Of the other claims that this library writes nothing is
said here. Nothing comes late (late := none): where `G.block` is the program's first block (a letter
here) the reply is the prover's message of the round REPLY, compared by the decision. To bind the
reply is then a load of `proofSound` itself: the state of a slot runs at `G.early x` to the end, and
what `early` drops stands in no query. At an `early` that drops more than the decision compares with
a message of the prover `proofSound` fails, and the theorem is empty there. Owed: the law that what
is got there is the reply's token; that the links at an instance and at its early part run alike.
That the real protocol meets the batch's clause at these values: no theorem of this library
concludes `CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T)` or `CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtSmallSize T)`, at any T;
it stands as a field of `RemainingSoundnessConditionsFromDryRunAtFullSize` | `RemainingSoundnessConditionsFromDryRunAtSmallSize`, as a premise, and in an equivalence between
T and `T.withId cfg` (Johnson/Flat/CommitCodeSound.lean). The library proves the clause of another
description: `CompilerSoundnessConditionStatements.proofSound` of the proof file's description built from public files in scope,
where protocolDataWellFormed says yes (`ProofSound`: `proofSound_of_verify`,
Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean); its decision is that description's own, not the
program's first block `G.block`. `G.early` is a letter: at early := id the reply would be hashed
first, which is not the programs' form: the programs' is "the reply's word wiped".
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.InnerInputOfThreeProtocols
import Johnson.Flat.SeedTwin
import Johnson.Flat.WireAt
import OnBytes.Flat.BigOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- All lists of answers are written with one number of digests. -/
theorem codeA_one {v s : ℕ} (c c' : (Fin v → Bool) × Fin s → GE) :
    (codeA c).length = (codeA c').length :=
  (codeA_length c).trans (codeA_length c').symm

/-- The test whether two seeds are equal, at the full size: the library's own, found by instance
search. A seed is one point of 29 coordinates with a factor that is not 0. -/
def seedEqFull : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ) := inferInstance

/-- The same at the small size: 19 coordinates. -/
def seedEqSmall : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ) := inferInstance

/-! ## The full-size files -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- The fields of an input, and of what the hypotheses name beside it, that are letters at
this size. -/
structure InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize where
  /-- the length of a file's salt in bytes -/
  salt : ℕ
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
           (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) t)
    (annOf (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
      (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) t)
  pl1 : PlainPart (shapeOf (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
           (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) t)
    (annOf (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
      (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) t)
  num : ℕ → Plains ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (KFullAt G + 1)
            (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL)) 256
  enc : KeyRoot 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : A.Mat → List Token → Option Token
  ISK : Type
  commit : A.Mat → Rom.OComp (typedOracleFamily 256 (KFullAt G + 1)
    (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
    (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL))
    (KeyRoot 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) × ISK)
  prove : ISK → (b : List (X × Unit)) →
    Rom.OComp (typedOracleFamily 256 (KFullAt G + 1)
      (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
      (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P)
        (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) b)
  bound : ℕ
  π₀ : KeyRoot 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) ×
    OfflineLinkOnlineProof 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P)
      (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256)
    (KeyRoot 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) ×
      OfflineLinkOnlineProof 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P)
        (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X

variable {A E G P}

/-- The body of a leaf is a string of bits. -/
abbrev InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.Bd (_ : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Type := List Bool

/-- The wiring is the written one (Johnson/Flat/WireAt.lean). -/
abbrev InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.W (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) :=
  wireFullAt A E G P T.salt

/-- The wiring has blocks enough for the record's seed. -/
theorem InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.hK (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : (seedBS recLg recS).b ≤ T.W.K :=
  seedKFull A E G P T.salt

/-- With the record's code and seed written. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.letters (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) :
    InnerCompilerInputFieldsOverThreeProtocols (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P where
  Bd := T.Bd
  W := T.W
  Sd := outOfDomainSampleQueryLayoutOfCode ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) T.Bd _ _ (v := frS.P.v) (lg := 29) (s := 1)
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS T.W.K T.hK) id
    seedEqFull
  cA := codeA (v := frS.P.v) (s := 1)
  r₀ := T.r₀
  p := T.p
  m := T.m
  enc := T.enc
  build := T.build
  nextToken := T.nextToken
  ISK := T.ISK
  commit := T.commit
  prove := T.prove
  bound := T.bound
  π₀ := T.π₀

/-- Every round's error is stated at 2^-128, counted with the round's proof of work: stated, not
proved, of the key file's and the proof file's rounds. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.names (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) :
    SoundnessAnalysisFieldsOverThreeProtocols (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P :=
  ⟨T.ext, T.εId, T.x₀, (2 : ℝ≥0∞)⁻¹ ^ 128⟩

/-- The input at this size. -/
def innerCompilerInputFromDryRunAtFullSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : InnerCompilerInput :=
  innerInputOfThreeProtocols (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P T.letters

/-- What the hypotheses name beside it. -/
def soundnessAnalysisDataFromDryRunAtFullSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : SoundnessAnalysisData (innerCompilerInputFromDryRunAtFullSize T) :=
  soundnessAnalysisDataOfThreeProtocols (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P T.letters T.names

/-- The named hypotheses that are left at this size: four, beside the theorem on codes. -/
structure RemainingSoundnessConditionsFromDryRunAtFullSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T)
  commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtFullSize T)
  sound      : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize T)

/-- Of the sixteen: what holds by a definition and says nothing of a protocol. -/
structure ByDefinitionFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Prop where
  noneColl : CompilerSoundnessConditionStatements.noneColl (r := innerCompilerInputFromDryRunAtFullSize T)

/-- Of the sixteen: what holds by construction: by unfolding and by lemmas that hold of all data:
nothing about this protocol is used. -/
structure ByConstructionFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Prop where
  keyLocal      : CompilerSoundnessConditionStatements.keyLocal (r := innerCompilerInputFromDryRunAtFullSize T)
  entryLocal    : CompilerSoundnessConditionStatements.entryLocal (r := innerCompilerInputFromDryRunAtFullSize T)
  proofLocal    : CompilerSoundnessConditionStatements.proofLocal (r := innerCompilerInputFromDryRunAtFullSize T)
  keyCoherent   : CompilerSoundnessConditionStatements.keyCoherent (r := innerCompilerInputFromDryRunAtFullSize T)
  entryCoherent : CompilerSoundnessConditionStatements.entryCoherent (r := innerCompilerInputFromDryRunAtFullSize T)
  proofCoherent : CompilerSoundnessConditionStatements.proofCoherent (r := innerCompilerInputFromDryRunAtFullSize T)
  answersLength : CompilerSoundnessConditionStatements.answersLength (r := innerCompilerInputFromDryRunAtFullSize T)

/-- Of the sixteen: what is proved with content: a fact about this protocol's own rounds or numbers,
or a law of a code that is written in this library, is used; the first under the theorem on codes.
-/
structure WithContentFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Prop where
  entrySound  : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataFromDryRunAtFullSize T)
  seedLaw     : CompilerSoundnessConditionStatements.seedLaw (soundnessAnalysisDataFromDryRunAtFullSize T)
  answersCode : CompilerSoundnessConditionStatements.answersCode (r := innerCompilerInputFromDryRunAtFullSize T)

/-- Of the sixteen: what is true of a wiring of our own choice: that the programs are wired so is
stated by no theorem; the two big files' data fail closed: where a test on the dry runs fails the
laws hold of a verifier that accepts nothing. -/
structure AtOurWiringFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Prop where
  wires : CompilerSoundnessConditionStatements.wires (r := innerCompilerInputFromDryRunAtFullSize T)

theorem byDefinitionFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : ByDefinitionFull T :=
  ⟨(threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).obj_noneColl P⟩

set_option maxRecDepth 20000 in
theorem byConstructionFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : ByConstructionFull T where
  keyLocal := (threeProtocolsFromDryRunAtFullSize_local A (relationsAndEncodingOfClaims A E) G).1
  entryLocal := (threeProtocolsFromDryRunAtFullSize_local A (relationsAndEncodingOfClaims A E) G).2.1
  proofLocal := (threeProtocolsFromDryRunAtFullSize_local A (relationsAndEncodingOfClaims A E) G).2.2
  keyCoherent := (threeProtocolsFromDryRunAtFullSize_coherent A (relationsAndEncodingOfClaims A E) G).1
  entryCoherent := threeProtocolsFromDryRunAtFullSize_entryCoherent A (relationsAndEncodingOfClaims A E) G
  proofCoherent := (threeProtocolsFromDryRunAtFullSize_coherent A (relationsAndEncodingOfClaims A E) G).2
  answersLength := codeA_one

set_option maxRecDepth 20000 in
/-- Under the theorem on codes. -/
theorem entrySoundFromDryRunAtFullSize (hA : BCHKS46At GF GE) (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataFromDryRunAtFullSize T) := by
  obtain ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtFullSize_entrySound A (relationsAndEncodingOfClaims A E) G hA
  refine ⟨ε, ?_, hs⟩
  show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsFull)) ε) _
  rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
  exact hb

set_option maxRecDepth 20000 in
/-- Under no hypothesis. -/
theorem seedLawFromDryRunAtFullSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : CompilerSoundnessConditionStatements.seedLaw (soundnessAnalysisDataFromDryRunAtFullSize T) :=
  outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entryFull_seedLawK A (relationsAndEncodingOfClaims A E) T.W.K T.hK y

set_option maxRecDepth 20000 in
/-- Under no hypothesis. -/
theorem answersCodeFromDryRunAtFullSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) :
    CompilerSoundnessConditionStatements.answersCode (r := innerCompilerInputFromDryRunAtFullSize T) := codeA_inj

set_option maxRecDepth 20000 in
/-- Under no hypothesis: the laws of the wires, at the written wiring: a wiring of our own choice.
-/
theorem wiresFromDryRunAtFullSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : CompilerSoundnessConditionStatements.wires (r := innerCompilerInputFromDryRunAtFullSize T) :=
  wiresFullAt A E G P T.salt

theorem atOurWiringFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : AtOurWiringFull T :=
  ⟨wiresFromDryRunAtFullSize T⟩

set_option maxRecDepth 20000 in
theorem withContentFull (hA : BCHKS46At GF GE) (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) :
    WithContentFull T where
  entrySound := entrySoundFromDryRunAtFullSize hA T
  seedLaw := seedLawFromDryRunAtFullSize T
  answersCode := answersCodeFromDryRunAtFullSize T

/-- The sixteen of `CompilerSoundnessConditionsWithMeaning`, from the four and the theorem on codes. -/
theorem RemainingSoundnessConditionsFromDryRunAtFullSize.holes (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P}
    (h : RemainingSoundnessConditionsFromDryRunAtFullSize T) : CompilerSoundnessConditionsWithMeaning (soundnessAnalysisDataFromDryRunAtFullSize T) where
  noneColl := (byDefinitionFull T).noneColl
  keySound := h.keySound
  entrySound := (withContentFull hA T).entrySound
  proofSound := h.proofSound
  keyLocal := (byConstructionFull T).keyLocal
  entryLocal := (byConstructionFull T).entryLocal
  proofLocal := (byConstructionFull T).proofLocal
  keyCoherent := (byConstructionFull T).keyCoherent
  entryCoherent := (byConstructionFull T).entryCoherent
  proofCoherent := (byConstructionFull T).proofCoherent
  seedLaw := (withContentFull hA T).seedLaw
  wires := (atOurWiringFull T).wires
  answersCode := (withContentFull hA T).answersCode
  answersLength := (byConstructionFull T).answersLength
  commitment := h.commitment
  sound := h.sound

/-- Under the four named hypotheses `RemainingSoundnessConditionsFromDryRunAtFullSize T` and the theorem on codes (hypotheses of the
theorem: Lean's list of axioms does not show them): the theorem on innerCompiledVerifier at this size, over
the compiled verifier that hashes a file as three chains. -/
theorem innerCompiledVerifierSoundFromDryRunAtFullSize (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P} (h : RemainingSoundnessConditionsFromDryRunAtFullSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  innerCompiledVerifier_sound _ (h.holes hA)

/-- The same at `G := bigOf U rec₀` (OnBytes/Flat/BigOf.lean): the proof file's first block is
`Proof.firstBlock` at the letters `U.links`, `U.reply`, and the dry runs are made at the record rec₀
and the instance `U.x₀`. A special case of `innerCompiledVerifierSoundFromDryRunAtFullSize`. -/
theorem innerCompiledVerifierSoundFromDryRunAtFullSize_dry (hA : BCHKS46At GF GE) (U : Pub X) (rec₀ : RecFull)
    {P' : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigOf U rec₀)).Provers}
    {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E (bigOf U rec₀) P'} (h : RemainingSoundnessConditionsFromDryRunAtFullSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  innerCompiledVerifierSoundFromDryRunAtFullSize hA h

end

/-! ## The small files -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- The fields of an input, and of what the hypotheses name beside it, that are letters at
this size. -/
structure InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize where
  /-- the length of a file's salt in bytes -/
  salt : ℕ
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
           (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) t)
    (annOf (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
      (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) t)
  pl1 : PlainPart (shapeOf (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
           (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) t)
    (annOf (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
      (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) t)
  num : ℕ → Plains ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (KSmallAt G + 1)
            (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL)) 256
  enc : KeyRoot 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : A.Mat → List Token → Option Token
  ISK : Type
  commit : A.Mat → Rom.OComp (typedOracleFamily 256 (KSmallAt G + 1)
    (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
    (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL))
    (KeyRoot 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) × ISK)
  prove : ISK → (b : List (X × Unit)) →
    Rom.OComp (typedOracleFamily 256 (KSmallAt G + 1)
      (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
      (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P)
        (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) b)
  bound : ℕ
  π₀ : KeyRoot 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) ×
    OfflineLinkOnlineProof 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P)
      (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256)
    (KeyRoot 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) ×
      OfflineLinkOnlineProof 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P)
        (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X

variable {A E G P}

/-- The body of a leaf is a string of bits. -/
abbrev InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.Bd (_ : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : Type := List Bool

/-- The wiring is the written one (Johnson/Flat/WireAt.lean). -/
abbrev InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.W (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) :
    QueryLayout 256 (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
            (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) :=
  wireSmallAt A E G P T.salt

/-- The wiring has blocks enough for the record's seed. -/
theorem InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.hK (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : (seedBS 19 1).b ≤ T.W.K :=
  seedKSmall A E G P T.salt

/-- With the record's code and seed written. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.letters (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) :
    InnerCompilerInputFieldsOverThreeProtocols (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P where
  Bd := T.Bd
  W := T.W
  Sd := outOfDomainSampleQueryLayoutOfCode ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) T.Bd _ _ (v := srS.P.v) (lg := 19) (s := 1)
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK srT 19 1 T.W.K T.hK) id seedEqSmall
  cA := codeA (v := srS.P.v) (s := 1)
  r₀ := T.r₀
  p := T.p
  m := T.m
  enc := T.enc
  build := T.build
  nextToken := T.nextToken
  ISK := T.ISK
  commit := T.commit
  prove := T.prove
  bound := T.bound
  π₀ := T.π₀

/-- Every round's error is stated at 2^-128, counted with the round's proof of work: stated, not
proved, of the key file's and the proof file's rounds. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.names (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) :
    SoundnessAnalysisFieldsOverThreeProtocols (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P :=
  ⟨T.ext, T.εId, T.x₀, (2 : ℝ≥0∞)⁻¹ ^ 128⟩

/-- The input at this size. -/
def innerCompilerInputFromDryRunAtSmallSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : InnerCompilerInput :=
  innerInputOfThreeProtocols (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P T.letters

/-- What the hypotheses name beside it. -/
def soundnessAnalysisDataFromDryRunAtSmallSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : SoundnessAnalysisData (innerCompilerInputFromDryRunAtSmallSize T) :=
  soundnessAnalysisDataOfThreeProtocols (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P T.letters T.names

/-- The named hypotheses that are left at this size: four, beside the theorem on codes. Of these
`proofSound` cannot be met by the small example's protocol at the written claim `claimsSmall`, and
is not expected to be met at `claimsLedger`, `claimsReq` (why: the head's Limits): by reading: no
theorem. -/
structure RemainingSoundnessConditionsFromDryRunAtSmallSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtSmallSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtSmallSize T)
  commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtSmallSize T)
  sound      : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtSmallSize T)

/-- Of the sixteen: what holds by a definition and says nothing of a protocol. -/
structure ByDefinitionSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : Prop where
  noneColl : CompilerSoundnessConditionStatements.noneColl (r := innerCompilerInputFromDryRunAtSmallSize T)

/-- Of the sixteen: what holds by construction: by unfolding and by lemmas that hold of all data:
nothing about this protocol is used. -/
structure ByConstructionSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : Prop where
  keyLocal      : CompilerSoundnessConditionStatements.keyLocal (r := innerCompilerInputFromDryRunAtSmallSize T)
  entryLocal    : CompilerSoundnessConditionStatements.entryLocal (r := innerCompilerInputFromDryRunAtSmallSize T)
  proofLocal    : CompilerSoundnessConditionStatements.proofLocal (r := innerCompilerInputFromDryRunAtSmallSize T)
  keyCoherent   : CompilerSoundnessConditionStatements.keyCoherent (r := innerCompilerInputFromDryRunAtSmallSize T)
  entryCoherent : CompilerSoundnessConditionStatements.entryCoherent (r := innerCompilerInputFromDryRunAtSmallSize T)
  proofCoherent : CompilerSoundnessConditionStatements.proofCoherent (r := innerCompilerInputFromDryRunAtSmallSize T)
  answersLength : CompilerSoundnessConditionStatements.answersLength (r := innerCompilerInputFromDryRunAtSmallSize T)

/-- Of the sixteen: what is proved with content: a fact about this protocol's own rounds or numbers,
or a law of a code that is written in this library, is used; the first under the theorem on codes.
-/
structure WithContentSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : Prop where
  entrySound  : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataFromDryRunAtSmallSize T)
  seedLaw     : CompilerSoundnessConditionStatements.seedLaw (soundnessAnalysisDataFromDryRunAtSmallSize T)
  answersCode : CompilerSoundnessConditionStatements.answersCode (r := innerCompilerInputFromDryRunAtSmallSize T)

/-- Of the sixteen: what is true of a wiring of our own choice: that the programs are wired so is
stated by no theorem; the two big files' data fail closed: where a test on the dry runs fails the
laws hold of a verifier that accepts nothing. -/
structure AtOurWiringSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : Prop where
  wires : CompilerSoundnessConditionStatements.wires (r := innerCompilerInputFromDryRunAtSmallSize T)

theorem byDefinitionSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : ByDefinitionSmall T :=
  ⟨(threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).obj_noneColl P⟩

set_option maxRecDepth 20000 in
theorem byConstructionSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : ByConstructionSmall T where
  keyLocal := (threeProtocolsFromDryRunAtSmallSize_local A (relationsAndEncodingOfClaims A E) G).1
  entryLocal := (threeProtocolsFromDryRunAtSmallSize_local A (relationsAndEncodingOfClaims A E) G).2.1
  proofLocal := (threeProtocolsFromDryRunAtSmallSize_local A (relationsAndEncodingOfClaims A E) G).2.2
  keyCoherent := (threeProtocolsFromDryRunAtSmallSize_coherent A (relationsAndEncodingOfClaims A E) G).1
  entryCoherent := threeProtocolsFromDryRunAtSmallSize_entryCoherent A (relationsAndEncodingOfClaims A E) G
  proofCoherent := (threeProtocolsFromDryRunAtSmallSize_coherent A (relationsAndEncodingOfClaims A E) G).2
  answersLength := codeA_one

set_option maxRecDepth 20000 in
/-- Under the theorem on codes. -/
theorem entrySoundFromDryRunAtSmallSize (hA : BCHKS46At GF GE) (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataFromDryRunAtSmallSize T) := by
  obtain ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtSmallSize_entrySound A (relationsAndEncodingOfClaims A E) G hA
  refine ⟨ε, ?_, hs⟩
  show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsSmall)) ε) _
  rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
  exact hb

set_option maxRecDepth 20000 in
/-- Under no hypothesis. -/
theorem seedLawFromDryRunAtSmallSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : CompilerSoundnessConditionStatements.seedLaw (soundnessAnalysisDataFromDryRunAtSmallSize T) :=
  outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entrySmall_seedLawK A (relationsAndEncodingOfClaims A E) T.W.K T.hK y

set_option maxRecDepth 20000 in
/-- Under no hypothesis. -/
theorem answersCodeFromDryRunAtSmallSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) :
    CompilerSoundnessConditionStatements.answersCode (r := innerCompilerInputFromDryRunAtSmallSize T) := codeA_inj

set_option maxRecDepth 20000 in
/-- Under no hypothesis: the laws of the wires, at the written wiring: a wiring of our own choice.
-/
theorem wiresFromDryRunAtSmallSize (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : CompilerSoundnessConditionStatements.wires (r := innerCompilerInputFromDryRunAtSmallSize T) :=
  wiresSmallAt A E G P T.salt

theorem atOurWiringSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : AtOurWiringSmall T :=
  ⟨wiresFromDryRunAtSmallSize T⟩

set_option maxRecDepth 20000 in
theorem withContentSmall (hA : BCHKS46At GF GE) (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) :
    WithContentSmall T where
  entrySound := entrySoundFromDryRunAtSmallSize hA T
  seedLaw := seedLawFromDryRunAtSmallSize T
  answersCode := answersCodeFromDryRunAtSmallSize T

/-- The sixteen of `CompilerSoundnessConditionsWithMeaning`, from the four and the theorem on codes. -/
theorem RemainingSoundnessConditionsFromDryRunAtSmallSize.holes (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P}
    (h : RemainingSoundnessConditionsFromDryRunAtSmallSize T) : CompilerSoundnessConditionsWithMeaning (soundnessAnalysisDataFromDryRunAtSmallSize T) where
  noneColl := (byDefinitionSmall T).noneColl
  keySound := h.keySound
  entrySound := (withContentSmall hA T).entrySound
  proofSound := h.proofSound
  keyLocal := (byConstructionSmall T).keyLocal
  entryLocal := (byConstructionSmall T).entryLocal
  proofLocal := (byConstructionSmall T).proofLocal
  keyCoherent := (byConstructionSmall T).keyCoherent
  entryCoherent := (byConstructionSmall T).entryCoherent
  proofCoherent := (byConstructionSmall T).proofCoherent
  seedLaw := (withContentSmall hA T).seedLaw
  wires := (atOurWiringSmall T).wires
  answersCode := (withContentSmall hA T).answersCode
  answersLength := (byConstructionSmall T).answersLength
  commitment := h.commitment
  sound := h.sound

/-- Under the four named hypotheses `RemainingSoundnessConditionsFromDryRunAtSmallSize T` and the theorem on codes (hypotheses of the
theorem: Lean's list of axioms does not show them): the theorem on innerCompiledVerifier at this size, over
the compiled verifier that hashes a file as three chains. Of the four, `proofSound` cannot be met
by the small example's protocol at the written claim `claimsSmall`, and is not expected to be met at
`claimsLedger`, `claimsReq` (why: the head's Limits): by reading: no theorem. -/
theorem innerCompiledVerifierSoundFromDryRunAtSmallSize (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P} (h : RemainingSoundnessConditionsFromDryRunAtSmallSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtSmallSize T))
      (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtSmallSize T)) :=
  innerCompiledVerifier_sound _ (h.holes hA)

/-- The same at `G := bigOf U rec₀` (OnBytes/Flat/BigOf.lean): the proof file's first block is
`Proof.firstBlock` at the letters `U.links`, `U.reply`, and the dry runs are made at the record rec₀
and the instance `U.x₀`. A special case of `innerCompiledVerifierSoundFromDryRunAtSmallSize`. -/
theorem innerCompiledVerifierSoundFromDryRunAtSmallSize_dry (hA : BCHKS46At GF GE) (U : Pub X) (rec₀ : RecSmall)
    {P' : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigOf U rec₀)).Provers}
    {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E (bigOf U rec₀) P'} (h : RemainingSoundnessConditionsFromDryRunAtSmallSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtSmallSize T))
      (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtSmallSize T)) :=
  innerCompiledVerifierSoundFromDryRunAtSmallSize hA h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtFullSize
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtSmallSize
