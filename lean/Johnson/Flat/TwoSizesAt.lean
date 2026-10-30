-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TwoSizesAt.lean: the theorem on innerCompiledVerifier over the compiled verifier that hashes a
file as three chains (`innerCompiledVerifier_sound`, Johnson/Top/InnerCompiledVerifier.lean)
at three files of the makers' make, at the two sizes of the default setting, WITH THE
WRITTEN ROUNDS' DATA AND THE TWO DECISIONS AS LETTERS (`threeProtocolsWithFixedLinkAtFullSize`, `threeProtocolsWithFixedLinkAtSmallSize`,
Johnson/Flat/WiresAtSizes.lean: the `filesAt`, called).

Why. Johnson/Flat/TwoSizes.lean has the theorem at `threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G`, where the data of
the key file's and the proof file's rounds come of a dry run of the verifier program's blocks and
the two decisions are that program's. Of the sixteen named hypotheses twelve hold there, and
none of the twelve proofs reads a decision; of the data they read numbers alone. So they hold
at every decision on the three views and at every data that pass tests on numbers.

Definitions, statements and proofs. The letters (`InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize` and what is made of it) are
those of TwoSizes.lean's sections, with `threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G` turned into `threeProtocolsWithFixedLinkAtFullSize …`,
`wireFullAt` into `wireOfFull`, `KFullAt G` into a letter K; the salt's length is a letter of the
files; four fields are added: depthReqT, hSeed, εs, hε.

Main names (Small for Full at the small size).
  `InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize`: the fields of an input, and of what the hypotheses name beside it, that are
    letters. It fills the records `InnerCompilerInputFieldsOverThreeProtocols`, `SoundnessAnalysisFieldsOverThreeProtocols` (Johnson/Flat/InnerInputOfThreeProtocols.lean) by
    `T.letters`, `T.names`, with the wiring, the seed's record and the answers' code laid.
    `innerCompilerInputWithFixedLinkAtFullSize T` is `innerInputOfThreeProtocols (threeProtocolsWithFixedLinkAtFullSize …) P T.letters` and `soundnessAnalysisDataWithFixedLinkAtFullSize T` is
    `soundnessAnalysisDataOfThreeProtocols (threeProtocolsWithFixedLinkAtFullSize …) P T.letters T.names`, by definition; the configuration is
    `DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)`.
  `RemainingSoundnessConditionsWithFixedLinkAtFullSize T`: keySound, proofSound, commitment.
  `compilerSoundnessConditionsWithFixedLinkAtFullSize`: the fifteen named hypotheses of `CompilerSoundnessConditions`, from these three, the theorem on codes
    and five tests on numbers.
  `innerCompiledVerifierSoundWithFixedLinkAtFullSize_for`: `innerCompiledVerifier_soundFor` there: for any claim on the index (`A.Mat`), under
    `CompilerSoundnessConditionStatements.soundFor`.
  `innerCompiledVerifierSoundWithFixedLinkAtFullSize`: `innerCompiledVerifier_sound` there: at "the output tokens are the model's".

Which of the sixteen holds how. At every data and every two decisions: noneColl, the three
Local, the three Coherent, answersCode, answersLength. seedLaw: wherever the wiring has blocks
enough for the record's seed (hSeed), at every εs ≥ 2^-128. entrySound: under the theorem on codes
(`Cb.BCHKS46At`, which this library proves in Cb/Bridge/ from lean/ThirdParty/: files adapted
from ArkLib and Mathlib (lean/LIMITS.md, L15)), at
every εs ≥ 2^-128. wires: under five tests on numbers, each with code: no round of the three files
has more than K blocks (`kThree`), and in neither whole file a round has more than 64 bits of work
(`WholeD.workFit`) or a tree deeper than 63 (`WholeD.depthFit`). Left: keySound, proofSound,
commitment, and the meaning (sound, or soundFor at a claim).

Does not show: any of the four that are left. Limits: what the heads of Johnson/Flat/TwoSizes.lean,
OnBytes/Flat/FilesAt.lean and Johnson/Top/InnerCompiledVerifier.lean list holds here too, at letters.

A HOLLOW VALUE MEETS ALL SIXTEEN (arguments, no theorems; at any T that there is). With two
decisions that say no to everything the twelve hold and keySound and proofSound hold for nothing; at
T.εId := ⊤ commitment holds; at a T.build that refuses everything the meaning holds. And whatever
the decisions are: at T.num := fun _ _ => false, or at such a T.build, the compiled verifier refuses
every proof (its yes begins with `S.num …`: Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean), and the theorems
below are true and empty at that T. That hypotheses are met is no news without proofs that the
verifier accepts.

εs IS BOUNDED FROM BELOW ALONE. The two whole files' verifiers test every round's proof of work
whatever the decisions say, and a round's error is a count of verifier messages, which hold the test
bits: so from εs = 2^-w on, w the most work of a round of the file (at most 64 under wK, wP; a
shared round of the key file counts 2 ^ T.depthReqT times), the work alone gives keySound and
proofSound, at any decision (a reckoning, no theorem). Below that (2^-128 lies below it, since w ≤
64) two decisions that say yes to everything make the two false (an argument, no theorem). A larger
εs is paid in `compiledSoundnessError`, whose first term is 5 (t + tVC + 1) · εs; T.εId stands in that
bound too, and has no ceiling. One bound εs serves the key file's, the entry file's and the proof
file's rounds and the seed; keySound and proofSound are asked at it, the proof file's for 2 ^
depthReq slots at once (depthReq is a letter: at 0 there is one slot and no batch). keySound's
factor 2 ^ T.depthReqT is a field that whoever fills T picks. entrySound's 2^-128 counts the rounds'
work: at six rounds of the full size and four of the small one 32 of the 128 bits are work
(OnBytes/Flat/FilesAt.lean's head).

TEN LETTERS THAT THE COMPILED VERIFIER READS ARE TIED TO NOTHING HERE: t, cfg, shape, pl0, pl1, num,
r₀, p, enc, build; two more, bound and π₀, are the committer's and the honest prover's alone, and
tied to nothing either. Above all T.num: the compiled verifier calls it on a proof string's number
and the proof file's plain parts, and no law pins it: what it is meant to test stands at the field
(`OutOfDomainSampleQueryLayout.num`, Johnson/TypedOracleCompiler/RecCompile/Seeds.lean); nothing holds a value to that. "The model" of
`innerCompiledVerifierSoundWithFixedLinkAtFullSize`'s claim is the letter T.nextToken. LAWS STAND IN THE TYPES OF THE LETTERS AND ARE
COUNTED NOWHERE: T.m : OracleCoding …: one coding of all hash queries in one hash function, one to one and
onto all bit strings; A.mat_cut. NO INHABITANT OF `InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize` | `Small` STANDS: none is
laid, at any data. rK, rP are records whose answers stand as the silent rounds' fixed messages: the
compiled verifier reads these where a component is not sent. DK.a, DP.a are idle: `WholeD.at` lays
the decoder's depth over them.

NOTHING HERE HAS CODE BY THIS FILE's WORD (a noncomputable section; runK, runP are any functions):
it is the frame as a statement, not as a term that runs. Every letter is bound outside the
probability, so none hangs on the drawn hash function here. Whoever lays values for real files keeps
the hash function's answers out of runK, runP, rK, rP, r₀ and π₀ (DK, DP hold none by their types):
they are to enter through the seed's record, the answers' code, m and enc alone.

THE ENTRY FILE's PROTOCOL IS THE WRITTEN LINK (`linkSibFull`, `linkSibSmall`), WHOSE DECISION IS A
RUN OF THE VERIFIER PROGRAM's OWN ROUTINE (`decFullX`, `decSmallX`, OnBytes/Flat/LinkSibAt.lean);
entrySound is a theorem on it. It is the description's entry part, with the program's run and the
literal of a digest in it; Johnson/Flat/Dec/TwoSizesAt.lean is this file's twin with the entry
file's rounds' data, openings and decision as letters.

NOTHING COMES LATE (late := none), AND `early` IS A LETTER: the state of a slot runs at `early x` to
the end, and what `early` drops stands in no query: to bind it is a load of proofSound itself. At an
`early` that drops more than runP compares with a message of the prover, at an εs below the work's
bound and a runP that accepts an honest prover's proofs, proofSound is not expected to be met: not
free, but out of reach (by reading: no theorem); at a hollow decision it stays free. At early := id
the reply would be hashed first, which is not the programs' form (Johnson/Flat/TwoSizes.lean's
head).

`wires` is true of a wiring of our own choice: that the programs are wired so is no statement of
Lean. That any data are those of a file, or come of a plan, is not shown. The decisions take three
views of the format's make: what a round draws is drawn by the format's sampler already. What the
silent rounds send is read by `silK`, `silP` alone: the joining round's run value and the seam's
bytes are read by no test of this make. No parser stands in `innerSystem`. `CompilerSoundnessConditionsWithMeaning` asks no
`ConfigurationWithOutOfDomainSample.Props`. Nothing on an honest prover, on completeness or on hiding. The letter K need not
reach the entry's description's own number of blocks (`frD.K`, a member of `KFullAt G`): no law here
asks it.

commitment can be proved by a general law where no bit string is the code of two keys
(`CompilerSoundnessConditionStatements.commitment_of_code`, Johnson/Top/CommitCodeAtInnerCompilerInput.lean), with T.ext and T.εId laid as that
law names: not called here. `relationsAndEncodingOfClaims A E` lays no cells: a witness has the type Unit, so a claim's
relation that has a witness (a policy's) must be closed under "there is" inside `A.Rel`; and a claim
on a model's weights (`MeetsPolicy`, lean/Policy/) is to be pulled back to `A.Mat`, or laid behind
the theorem by `SoundForWith.mapWeights`. At the small size what Johnson/Flat/TwoSizes.lean's head
says of `claimsSmall`, `claimsLedger` and `claimsReq` holds of data and decisions that accept the
small example's proofs.

That `innerCompiledVerifierSoundFromDryRunAtFullSize` (Johnson/Flat/TwoSizes.lean) is this file's theorem at the makers' data is not
stated: `threeProtocolsFromDryRunAtFullSize_eq_withFixedLink` and `wireFullK_eq_of` have the files and the wiring.
Johnson/Flat/TwoSizes.lean is imported for three names alone (`codeA_one`, `seedEqFull`,
`seedEqSmall`) and brings the makers' files and their dry runs beneath this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.WiresAtSizes
import Johnson.Flat.TwoSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The full-size files -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt K : ℕ)
  (P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers)

/-- The three files. -/
local notation "Ff" => threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt

/-- The fields of an input, and of what the hypotheses name beside it, that are letters at
this size. -/
structure InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize where
  /-- the depth of a request tree of the key file's test -/
  depthReqT : ℕ
  /-- the wiring has blocks enough for the record's seed -/
  hSeed : (seedBS recLg recS).b ≤ K + 1
  /-- the stated bound on a round's error: at least 2^-128, at which the entry file's rounds and the
  record's seed are proved -/
  εs : ℝ≥0∞
  hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
    (annOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
  pl1 : PlainPart (shapeOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
    (annOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
  num : ℕ → Plains ((Ff).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL)) 256
  enc : KeyRoot 256 ((Ff).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : A.Mat → List Token → Option Token
  ISK : Type
  commit : A.Mat → Rom.OComp (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Ff).withProvers P) (List Bool)
                 (Ff).annT (Ff).annL))
    (KeyRoot 256 ((Ff).withProvers P) × ISK)
  prove : ISK → (b : List (X × Unit)) → Rom.OComp (typedOracleFamily 256 (K + 1)
      (typedOracleCarrier ((Ff).withProvers P) (List Bool)
      (Ff).annT (Ff).annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((Ff).withProvers P) (Ff).annT (Ff).annL) b)
  bound : ℕ
  π₀ : KeyRoot 256 ((Ff).withProvers P) × OfflineLinkOnlineProof 256 ((Ff).withProvers P) (Ff).annT (Ff).annL
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256) (KeyRoot 256 ((Ff).withProvers P) ×
      OfflineLinkOnlineProof 256 ((Ff).withProvers P) (Ff).annT (Ff).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X

variable {A E DK DP runK runP rK rP depthReq early salt K P}

/-- The letters' type. It holds K, salt and P beside the files' letters. -/
local notation "Lf" => InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P

/-- The body of a leaf is a string of bits. -/
abbrev InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize.Bd (_ : Lf) : Type := List Bool

/-- The wiring is `wireOfFull` (Johnson/Flat/WiresAtSizes.lean). -/
abbrev InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize.W (T : Lf) :
    QueryLayout 256 (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) :=
  wireOfFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P K T.depthReqT

/-- The wiring has blocks enough for the record's seed. -/
theorem InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize.hK (T : Lf) : (seedBS recLg recS).b ≤ T.W.K :=
  T.hSeed

/-- With the record's code and seed written. -/
def InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize.letters (T : Lf) :
    InnerCompilerInputFieldsOverThreeProtocols (Ff) P where
  Bd := T.Bd
  W := T.W
  Sd := outOfDomainSampleQueryLayoutOfCode ((Ff).withProvers P) T.Bd _ _ (v := frS.P.v) (lg := 29) (s := 1)
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

/-- Every round's error is stated at εs, counted with the round's proof of work: stated, not proved,
of the key file's and the proof file's rounds. -/
def InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize.names (T : Lf) :
    SoundnessAnalysisFieldsOverThreeProtocols (Ff) P :=
  ⟨T.ext, T.εId, T.x₀, T.εs⟩

/-- The input at this size. -/
def innerCompilerInputWithFixedLinkAtFullSize (T : Lf) : InnerCompilerInput :=
  innerInputOfThreeProtocols (Ff) P T.letters

/-- What the hypotheses name beside it. -/
def soundnessAnalysisDataWithFixedLinkAtFullSize (T : Lf) : SoundnessAnalysisData (innerCompilerInputWithFixedLinkAtFullSize T) :=
  soundnessAnalysisDataOfThreeProtocols (Ff) P T.letters T.names

/-- The named hypotheses that are left at this size, beside the meaning and the theorem on codes. -/
structure RemainingSoundnessConditionsWithFixedLinkAtFullSize (T : Lf) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T)
  commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataWithFixedLinkAtFullSize T)

set_option maxRecDepth 20000 in
/-- Under the theorem on codes. -/
theorem entrySoundWithFixedLinkAtFullSize (hA : BCHKS46At GF GE) (T : Lf) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataWithFixedLinkAtFullSize T) := by
  obtain ⟨ε, hs, hb⟩ := linkSibFull_sound hA A (relationsAndEncodingOfClaims A E)
  refine ⟨ε, ?_, hs⟩
  show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsFull)) ε) _
  rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
  exact Err.Below.mono_bound T.hε hb

set_option maxRecDepth 20000 in
/-- **Twelve of the fifteen named hypotheses of `CompilerSoundnessConditions` hold at this make**, under the theorem on
codes and the premises on numbers: the fifteen, from these and the three of `RemainingSoundnessConditionsWithFixedLinkAtFullSize`. Two
premises more ride inside T: hSeed and hε. -/
theorem compilerSoundnessConditionsWithFixedLinkAtFullSize (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Lf}
    (h : RemainingSoundnessConditionsWithFixedLinkAtFullSize T) : CompilerSoundnessConditions (soundnessAnalysisDataWithFixedLinkAtFullSize T) where
  noneColl := (Ff).obj_noneColl P
  keySound := h.keySound
  entrySound := entrySoundWithFixedLinkAtFullSize hA T
  proofSound := h.proofSound
  keyLocal := (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).1
  entryLocal := (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2.1
  proofLocal := (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2.2
  keyCoherent := (threeProtocolsWithFixedLinkAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).1
  entryCoherent := threeProtocolsWithFixedLinkAtFullSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early
    salt
  proofCoherent := (threeProtocolsWithFixedLinkAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2
  seedLaw := outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
    le_trans (entryFull_seedLawK A (relationsAndEncodingOfClaims A E) T.W.K T.hK y) T.hε
  wires := wiresOfFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P K T.depthReqT hk
    wK dK wP dP
  answersCode := codeA_inj
  answersLength := codeA_one
  commitment := h.commitment

/-- **The compiler's theorem at this make, for any claim on the index**: `innerCompiledVerifier_soundFor`
(Johnson/Top/InnerCompiledVerifier.lean). Under: the theorem on codes (hA); five tests on numbers (hk, wK, dK,
wP, dP); keySound, proofSound and commitment (h); that the relaxed relation gives the claim (hs);
and, inside T, hSeed and hε. All are hypotheses of the theorem: Lean's list of axioms does not show
them. -/
theorem innerCompiledVerifierSoundWithFixedLinkAtFullSize_for (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Lf}
    (h : RemainingSoundnessConditionsWithFixedLinkAtFullSize T) (claim : A.Mat → List Token → List Token → Prop)
    (hs : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataWithFixedLinkAtFullSize T) claim) :
    SoundForWith (innerSystem (innerCompilerInputWithFixedLinkAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataWithFixedLinkAtFullSize T)) claim
      (compiledSoundnessError (soundnessAnalysisDataWithFixedLinkAtFullSize T)) :=
  innerCompiledVerifier_soundFor _ claim (compilerSoundnessConditionsWithFixedLinkAtFullSize hA hk wK dK wP dP h) hs

/-- **The same at the claim "the output tokens are the model's"** (the model is the letter
T.nextToken): `innerCompiledVerifier_sound`. Under the same hypotheses: hA; hk, wK, dK, wP, dP; the three of h;
hSeed and hε inside T; with the meaning (hs : `CompilerSoundnessConditionStatements.sound`) in `soundFor`'s place. -/
theorem innerCompiledVerifierSoundWithFixedLinkAtFullSize (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Lf}
    (h : RemainingSoundnessConditionsWithFixedLinkAtFullSize T) (hs : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataWithFixedLinkAtFullSize T)) :
    SoundForWith (innerSystem (innerCompilerInputWithFixedLinkAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataWithFixedLinkAtFullSize T))
      (innerSystem (innerCompilerInputWithFixedLinkAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataWithFixedLinkAtFullSize T)) :=
  innerCompiledVerifier_sound _ ⟨compilerSoundnessConditionsWithFixedLinkAtFullSize hA hk wK dK wP dP h, hs⟩

end

/-! ## The small files -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (DK DP : WholeD)
  (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall) (depthReq : ℕ)
  (early : X → X) (salt K : ℕ)
  (P : (threeProtocolsWithFixedLinkAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers)

/-- The three files. -/
local notation "Fs" => threeProtocolsWithFixedLinkAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt

/-- The fields of an input, and of what the hypotheses name beside it, that are letters at
this size. -/
structure InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize where
  /-- the depth of a request tree of the key file's test -/
  depthReqT : ℕ
  /-- the wiring has blocks enough for the record's seed -/
  hSeed : (seedBS 19 1).b ≤ K + 1
  /-- the stated bound on a round's error: at least 2^-128, at which the entry file's rounds and the
  record's seed are proved -/
  εs : ℝ≥0∞
  hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
    (annOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
  pl1 : PlainPart (shapeOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
    (annOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
  num : ℕ → Plains ((Fs).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL)) 256
  enc : KeyRoot 256 ((Fs).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : A.Mat → List Token → Option Token
  ISK : Type
  commit : A.Mat → Rom.OComp (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Fs).withProvers P) (List Bool)
                 (Fs).annT (Fs).annL))
    (KeyRoot 256 ((Fs).withProvers P) × ISK)
  prove : ISK → (b : List (X × Unit)) → Rom.OComp (typedOracleFamily 256 (K + 1)
      (typedOracleCarrier ((Fs).withProvers P) (List Bool)
      (Fs).annT (Fs).annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((Fs).withProvers P) (Fs).annT (Fs).annL) b)
  bound : ℕ
  π₀ : KeyRoot 256 ((Fs).withProvers P) × OfflineLinkOnlineProof 256 ((Fs).withProvers P) (Fs).annT (Fs).annL
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256) (KeyRoot 256 ((Fs).withProvers P) ×
      OfflineLinkOnlineProof 256 ((Fs).withProvers P) (Fs).annT (Fs).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X

variable {A E DK DP runK runP rK rP depthReq early salt K P}

/-- The letters' type. It holds K, salt and P beside the files' letters. -/
local notation "Ls" => InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize A E DK DP runK runP rK rP depthReq early salt K P

/-- The body of a leaf is a string of bits. -/
abbrev InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize.Bd (_ : Ls) : Type := List Bool

/-- The wiring is `wireOfSmall` (Johnson/Flat/WiresAtSizes.lean). -/
abbrev InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize.W (T : Ls) :
    QueryLayout 256 (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) :=
  wireOfSmall A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P K T.depthReqT

/-- The wiring has blocks enough for the record's seed. -/
theorem InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize.hK (T : Ls) : (seedBS 19 1).b ≤ T.W.K :=
  T.hSeed

/-- With the record's code and seed written. -/
def InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize.letters (T : Ls) :
    InnerCompilerInputFieldsOverThreeProtocols (Fs) P where
  Bd := T.Bd
  W := T.W
  Sd := outOfDomainSampleQueryLayoutOfCode ((Fs).withProvers P) T.Bd _ _ (v := srS.P.v) (lg := 19) (s := 1)
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

/-- Every round's error is stated at εs, counted with the round's proof of work: stated, not proved,
of the key file's and the proof file's rounds. -/
def InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize.names (T : Ls) :
    SoundnessAnalysisFieldsOverThreeProtocols (Fs) P :=
  ⟨T.ext, T.εId, T.x₀, T.εs⟩

/-- The input at this size. -/
def innerCompilerInputWithFixedLinkAtSmallSize (T : Ls) : InnerCompilerInput :=
  innerInputOfThreeProtocols (Fs) P T.letters

/-- What the hypotheses name beside it. -/
def soundnessAnalysisDataWithFixedLinkAtSmallSize (T : Ls) : SoundnessAnalysisData (innerCompilerInputWithFixedLinkAtSmallSize T) :=
  soundnessAnalysisDataOfThreeProtocols (Fs) P T.letters T.names

/-- The named hypotheses that are left at this size, beside the meaning and the theorem on codes. -/
structure RemainingSoundnessConditionsWithFixedLinkAtSmallSize (T : Ls) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtSmallSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtSmallSize T)
  commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataWithFixedLinkAtSmallSize T)

set_option maxRecDepth 20000 in
/-- Under the theorem on codes. -/
theorem entrySoundWithFixedLinkAtSmallSize (hA : BCHKS46At GF GE) (T : Ls) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataWithFixedLinkAtSmallSize T) := by
  obtain ⟨ε, hs, hb⟩ := linkSibSmall_sound hA A (relationsAndEncodingOfClaims A E)
  refine ⟨ε, ?_, hs⟩
  show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsSmall)) ε) _
  rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
  exact Err.Below.mono_bound T.hε hb

set_option maxRecDepth 20000 in
/-- **Twelve of the fifteen named hypotheses of `CompilerSoundnessConditions` hold at this make**, under the theorem on
codes and the premises on numbers: the fifteen, from these and the three of `RemainingSoundnessConditionsWithFixedLinkAtSmallSize`. Two
premises more ride inside T: hSeed and hε. -/
theorem compilerSoundnessConditionsWithFixedLinkAtSmallSize (hA : BCHKS46At GF GE) (hk : kThree .two DK srRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Ls}
    (h : RemainingSoundnessConditionsWithFixedLinkAtSmallSize T) : CompilerSoundnessConditions (soundnessAnalysisDataWithFixedLinkAtSmallSize T) where
  noneColl := (Fs).obj_noneColl P
  keySound := h.keySound
  entrySound := entrySoundWithFixedLinkAtSmallSize hA T
  proofSound := h.proofSound
  keyLocal := (threeProtocolsWithFixedLinkAtSmallSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).1
  entryLocal := (threeProtocolsWithFixedLinkAtSmallSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2.1
  proofLocal := (threeProtocolsWithFixedLinkAtSmallSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2.2
  keyCoherent := (threeProtocolsWithFixedLinkAtSmallSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).1
  entryCoherent := threeProtocolsWithFixedLinkAtSmallSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early
    salt
  proofCoherent := (threeProtocolsWithFixedLinkAtSmallSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early
    salt).2
  seedLaw := outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
    le_trans (entrySmall_seedLawK A (relationsAndEncodingOfClaims A E) T.W.K T.hK y) T.hε
  wires := wiresOfSmall A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P K T.depthReqT hk
    wK dK wP dP
  answersCode := codeA_inj
  answersLength := codeA_one
  commitment := h.commitment

/-- **The compiler's theorem at this make, for any claim on the index**: `innerCompiledVerifier_soundFor`
(Johnson/Top/InnerCompiledVerifier.lean). Under: the theorem on codes (hA); five tests on numbers (hk, wK, dK,
wP, dP); keySound, proofSound and commitment (h); that the relaxed relation gives the claim (hs);
and, inside T, hSeed and hε. All are hypotheses of the theorem: Lean's list of axioms does not show
them. -/
theorem innerCompiledVerifierSoundWithFixedLinkAtSmallSize_for (hA : BCHKS46At GF GE) (hk : kThree .two DK srRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Ls}
    (h : RemainingSoundnessConditionsWithFixedLinkAtSmallSize T) (claim : A.Mat → List Token → List Token → Prop)
    (hs : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataWithFixedLinkAtSmallSize T) claim) :
    SoundForWith (innerSystem (innerCompilerInputWithFixedLinkAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataWithFixedLinkAtSmallSize T)) claim
      (compiledSoundnessError (soundnessAnalysisDataWithFixedLinkAtSmallSize T)) :=
  innerCompiledVerifier_soundFor _ claim (compilerSoundnessConditionsWithFixedLinkAtSmallSize hA hk wK dK wP dP h) hs

/-- **The same at the claim "the output tokens are the model's"** (the model is the letter
T.nextToken): `innerCompiledVerifier_sound`. Under the same hypotheses: hA; hk, wK, dK, wP, dP; the three of h;
hSeed and hε inside T; with the meaning (hs : `CompilerSoundnessConditionStatements.sound`) in `soundFor`'s place. -/
theorem innerCompiledVerifierSoundWithFixedLinkAtSmallSize (hA : BCHKS46At GF GE) (hk : kThree .two DK srRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Ls}
    (h : RemainingSoundnessConditionsWithFixedLinkAtSmallSize T) (hs : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataWithFixedLinkAtSmallSize T)) :
    SoundForWith (innerSystem (innerCompilerInputWithFixedLinkAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataWithFixedLinkAtSmallSize T))
      (innerSystem (innerCompilerInputWithFixedLinkAtSmallSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataWithFixedLinkAtSmallSize T)) :=
  innerCompiledVerifier_sound _ ⟨compilerSoundnessConditionsWithFixedLinkAtSmallSize hA hk wK dK wP dP h, hs⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.compilerSoundnessConditionsWithFixedLinkAtFullSize
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundWithFixedLinkAtFullSize_for
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundWithFixedLinkAtFullSize
#print axioms VerifiableInference.OnPublicFiles.compilerSoundnessConditionsWithFixedLinkAtSmallSize
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundWithFixedLinkAtSmallSize_for
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundWithFixedLinkAtSmallSize
