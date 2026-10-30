-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/NamedReal.lean (the request's item is a letter `it`: Dec/MOneD.lean's head says why): at the full size: A NAMED SIDE THAT IS NOT HOLLOW, at the record T that a run reaches (`tAt`, TieAtValues.lean): the library's
own extractor behind the commitment and the library's own cost; and the hypothesis on the commitment PAID there.

Why. The conditional soundness theorem over the frame (`innerCompiledVerifierSoundAtFullSize_for`, Johnson/Flat/Dec/TwoSizesAt.lean) names, beside the verifier's letters, six more: the
model, an extractor, its cost, an instance, a bound εs. The one T that was filled until now (`tFilled`) lays a hollow side: an extractor that finds nothing, at cost
0. There the hypothesis `commitment` says that a proof is accepted, with no index found, with probability at most the other terms: false as soon as an honest
proof is accepted. So the theorem said nothing at the T that a run reaches. Here a side is laid at which that hypothesis is a theorem.
Main names.
  `namedReal … nextToken`: THE NAMED SIDE: ext := `keyCodeIndexExtractor` (Johnson/Top/CommitCodeAtInnerCompilerInput.lean: it looks for the key in the committer's query log) at the
    input of `tAt`; εId := `commitmentErrorOfKeyCode`: (t + 2)² / 2^256; x₀ := the plan's own request. TWO LETTERS ARE LEFT: the model `nextToken`, and εs, the stated bound on a
    round's error, with its lower bound 2^-128 (the frame's own hε). εs HAS NO UPPER BOUND IN THE TYPE: AT A LARGE εs THE HYPOTHESES THAT NAME IT COST NOTHING AND THE THEOREM's
    BOUND SAYS LITTLE (the proof file's from 2^-w on, w the most work of a round, at most 64): WHOEVER CALLS THIS NAMES εs. `namedAim`: at εs := 2^-128, the release's aim.
  `tReal`: `tAt` at that side. `seam_real`: its input's verifier is `tAt`'s at ANY named side (the frame's law): SO THE TIE FROM WHAT RUNS REACHES IT.
  `encF_is`, `enc_at`: the code of a key at `tAt` IS the `idCodeSeed` at the spelling `spellFull` and the bytes of c: by unfolding.
  `CommitmentAt` (a definition of its own), `commitment_at`: **`CompilerSoundnessConditionStatements.commitment` holds at `tReal`**: no premise beside `tAt`'s own four on data:
    `CompilerSoundnessConditionStatements.commitment_idSeed`.
  `hasCode_at`, `twoCodes_at`: CONTROLS: every key has a code there, and there are two keys with one root and one list of answers whose codes differ: so the code
    is not the one that gives no key a code, at which `commitment` holds idly.
  `error_at`: the theorem's bound there, written: soundnessBoundOverTypedOracles queryLayout εs t 0 + (t + 2)² / 2^256.
  `LeftThree`, `SoundAtReal` (a definition of its own), `sound_at_real`: the conditional theorem at `tReal`: WHAT IS STILL ASKED: `keySound`, `entrySound`, `proofSound`
    at εs · nine tests on numbers · the meaning of the relaxed relation for the claim.
  `code_told`: for the road on which T hangs on public digests (Johnson/Top/InnerCompiledVerifierByPublicReading.lean): no two pairs (c, key) have one code: its hypothesis `code`.
WHICH ROAD READS WHAT. On the road of a FIXED input (`innerCompiledVerifier_sound`) the named side is read: this file's `namedReal` is for it. On the TOLD road, the one that can
reach a description whose T hangs on c and the seven, the extractor and the cost are laid by the law itself (`LayoutsByPublicReading.beside`: the library's own) and N's two
fields are read by nobody: there `code_told` is what is asked.
Limits. (1) THE THREE HYPOTHESES THAT CARRY THE MATHEMATICS ARE NOT TOUCHED: `keySound`, `entrySound`, `proofSound` are asked, at εs. Nothing here says that they
hold at any decisions; at «always yes» they are false. (2) c IS A CONSTANT of this T: fixed before the hash function is drawn, which the format's
specification rules out for a model of the format (the limits of Johnson/Top/CommitCodeAtInnerCompilerInput.lean): the told road is the cure. (3) The extractor looks in the
COMMITTER's query log: a committer that never asked the hash function at its key's code is not caught by it but by the cost. (4) E, P and the model are letters: at
the hollow coding `codingH` the claims speak of nothing. Nothing on completeness or hiding.

-/
import Johnson.Top.Fire.Code.Seam
import Johnson.Top.Fire.Code.TieFilled
import Johnson.Flat.CommitCodeSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)
open PV.EntryFive
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open PV.OkOwn (okOwnF)
open OnBytes.K.IdTable (spellAns spellSeed spellAns_inj spellSeed_inj)
open TypedOracleCompiler.VerifiableInference.Rec (IdSpellS idCodeSeed)

/-- The value that is laid for the code of a key is the code at the spelling: at any three files of the full size's configuration. -/
theorem encF_is {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
    (F : OnBytes.Flat.Files (DecR.configurationOfStoredTable A R)) (P : F.Provers) (c : Dig 256) (k : KeyRoot 256 (F.withProvers P)) :
    PV.EncId.encF c k.cm k.rcd = idCodeSeed (spellFull F P) (digToBytes c) [] k :=
  congrArg OnBytes.Tie.idCodeS rfl

attribute [local irreducible] PV.EncId.encF

/-- **THE NAMED SIDE THAT IS NOT HOLLOW.** The extractor reads of the input its coding, its wire and its code of a key alone: these are the verifier's side's, so the
hollow side in the term is idle (`ext_real`). -/
def namedReal (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (nextToken : A.Mat → List Token → Option Token) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) :
    NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P where
  nextToken := nextToken
  ext := keyCodeIndexExtractor (innerCompilerInputAtFullSize (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK (namedH A E G DK DP runK runP dec P G.z₀.1) pdL))
  εId := commitmentErrorOfKeyCode
  x₀ := G.z₀.1
  εs := εs
  hε := hε

/-- The same at the release's aim for a round's error. -/
abbrev namedAim (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (nextToken : A.Mat → List Token → Option Token) :=
  namedReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken ((2 : ℝ≥0∞)⁻¹ ^ 128) (le_refl _)

/-- `tAt` at that side. -/
abbrev tReal (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (nextToken : A.Mat → List Token → Option Token) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) (d₀ : Dig 256) :=
  tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK (namedReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε) d₀

section
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (nextToken : A.Mat → List Token → Option Token) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) (d₀ : Dig 256)

/-- Its verifier is `tAt`'s at any named side: so what the tie reaches at one side it reaches at this one. -/
theorem seam_real (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) :
    (innerSystem (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀))).verify =
      (innerSystem (innerCompilerInputAtFullSize (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀))).verify := rfl

/-- The extractor that is laid is the library's at this very input. -/
theorem ext_real :
    (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)).ext = keyCodeIndexExtractor (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)) := rfl

/-- **The code of a key at `tAt` is the code at the spelling and the bytes of c.** -/
theorem enc_at :
    (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)).keyCode =
      idCodeSeed (spellFull (FsAtR A E G DK DP runK runP dec) P) (digToBytes (bytesToDig c)) [] :=
  funext fun k => encF_is (FsAtR A E G DK DP runK runP dec) P (bytesToDig c) k

end

/-- **The hypothesis on the commitment, at the T that a run reaches and the side that is not hollow.** -/
def CommitmentAt : Prop :=
  ∀ (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (nextToken : A.Mat → List Token → Option Token) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) (d₀ : Dig 256),
    CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀))

set_option maxHeartbeats 1000000 in
theorem commitment_at : CommitmentAt :=
  fun A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀ =>
  CompilerSoundnessConditionStatements.commitment_idSeed (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀))
    (spellFull (FsAtR A E G DK DP runK runP dec) P) (spellAns_inj frS.P.v 1) (spellSeed_inj 29 1) (digToBytes (bytesToDig c))
    (enc_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀) (ext_real A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀) rfl

section
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (nextToken : A.Mat → List Token → Option Token) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) (d₀ : Dig 256)

/-- A control: every key has a code there. -/
theorem hasCode_at (k : KeyRoot 256 ((FsAtR A E G DK DP runK runP dec).withProvers P)) :
    ∃ code, (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)).keyCode k = some code := by
  rw [enc_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀]
  exact hasCode_spellFull (FsAtR A E G DK DP runK runP dec) P (digToBytes (bytesToDig c)) (size_digToBytes _) k

/-- A control: two keys with one root and one list of answers, and different seeds, have different codes there. -/
theorem twoCodes_at :
    ∃ k k' : KeyRoot 256 ((FsAtR A E G DK DP runK runP dec).withProvers P), k.cm = k'.cm ∧ k.rcd.2 = k'.rcd.2 ∧ k.rcd.1 ≠ k'.rcd.1 ∧
      (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)).keyCode k ≠ (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)).keyCode k' := by
  rw [enc_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀]
  exact twoCodes_spellFull (FsAtR A E G DK DP runK runP dec) P (digToBytes (bytesToDig c)) (size_digToBytes _)

/-- The theorem's bound there, written. -/
theorem error_at (t : ℕ) :
    compiledSoundnessError (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)) t =
      soundnessBoundOverTypedOracles (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)).queryLayout εs t 0 + (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := rfl

/-- The three named hypotheses that are still asked at `tReal`: each at εs. -/
structure LeftThree : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀))
  entrySound : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀))
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀))

end

/-- **The conditional theorem at the T that a run reaches, its named side not hollow.** -/
def SoundAtReal : Prop :=
  ∀ (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (nextToken : A.Mat → List Token → Option Token) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) (d₀ : Dig 256)
    (_ : kThree .two DK [] DP ≤ KF DK DP)
    (_ : ∀ d ∈ dsF, (bsRound .two d.entry d.kind).b ≤ KF DK DP) (_ : ∀ d ∈ dsF, d.entry.work ≤ 64)
    (_ : ∀ d ∈ dsF, ∀ n ∈ d.opens, n < 2 ^ 16) (_ : ∀ d ∈ dsF, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (_ : DK.workFit = true) (_ : DK.depthFit = true) (_ : DP.workFit = true) (_ : DP.depthFit = true)
    (_ : LeftThree A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)
    (claim : A.Mat → List Token → List Token → Prop)
    (_ : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)) claim),
    SoundForWith (innerSystem (innerCompilerInputAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)))
      (compiledIndexExtractor (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀))) claim
      (compiledSoundnessError (soundnessAnalysisDataAtFullSize (tReal A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀)))

set_option maxHeartbeats 1000000 in
theorem sound_at_real : SoundAtReal :=
  fun A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀ hk bL wLk own dL wK dKf wP dPf h claim hs =>
  innerCompiledVerifierSoundAtFullSize_for hk bL wLk own dL wK dKf wP dPf
    ⟨h.keySound, h.entrySound, h.proofSound, commitment_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK nextToken εs hε d₀⟩ claim hs

/-- **For the told road: no two pairs (c, key) have one code.** -/
theorem code_told (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (DK DP : WholeD)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool) (P : (FsAtR A E G DK DP runK runP dec).Provers) :
    ZKCP.CodeIsOneToOne fun k : Dig 256 × KeyRoot 256 ((FsAtR A E G DK DP runK runP dec).withProvers P) =>
      PV.EncId.encF k.1 k.2.cm k.2.rcd := by
  intro k k' code h h'
  have h1 := (encF_is (FsAtR A E G DK DP runK runP dec) P k.1 k.2).symm.trans h
  have h1' := (encF_is (FsAtR A E G DK DP runK runP dec) P k'.1 k'.2).symm.trans h'
  have q := TypedOracleCompiler.VerifiableInference.Rec.IdSpellS.keyAt_inj (spellFull (FsAtR A E G DK DP runK runP dec) P)
    (spellAns_inj frS.P.v 1) (spellSeed_inj 29 1) (cfg := digToBytes k.1) (cfg' := digToBytes k'.1) (told := []) (told' := [])
    (k := k.2) (k' := k'.2) (OnBytes.Tie.idCodeS_oneToOne _ _ code h1 h1')
  exact Prod.ext (by rw [← OnBytes.K.Arm.bytesToDig_digToBytes k.1, q.1, OnBytes.K.Arm.bytesToDig_digToBytes]) q.2.2

end LPFD.Full

#print axioms LPFD.Full.encF_is
#print axioms LPFD.Full.namedReal
#print axioms LPFD.Full.seam_real
#print axioms LPFD.Full.ext_real
#print axioms LPFD.Full.enc_at
#print axioms LPFD.Full.CommitmentAt
#print axioms LPFD.Full.commitment_at
#print axioms LPFD.Full.hasCode_at
#print axioms LPFD.Full.twoCodes_at
#print axioms LPFD.Full.error_at
#print axioms LPFD.Full.SoundAtReal
#print axioms LPFD.Full.sound_at_real
#print axioms LPFD.Full.code_told
