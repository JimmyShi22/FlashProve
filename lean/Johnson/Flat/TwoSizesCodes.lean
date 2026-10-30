-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TwoSizesCodes.lean: five theorems of Johnson/Flat/TwoSizes.lean and
Johnson/Flat/ThreeFull.lean that are stated under the hypothesis on codes (`BCHKS46At GF GE`), with
that one hypothesis filled. The named hypotheses that are left are unproved.

What this file states. Each has the statement of the theorem whose name it bears before `_codes`,
less that hypothesis; every other hypothesis stays. Its proof is one application of that theorem at
`Cb.Gl.bchks46At` (Cb/Bridge/GlCodesProved.lean), which rests on the files under lean/ThirdParty/:
Lean text adapted from ArkLib and Mathlib (lean/LIMITS.md, L15; what it is and
whence: lean/ThirdParty/README.md). `GF` and `GE` (OnBytes/Slice/Draws.lean)
are `Cb.Gl.F` and `Cb.Gl.E` by abbreviation. The forms with the hypothesis stand in their
files. Seven others with that hypothesis have no such form here: `withContentFull`,
`RemainingSoundnessConditionsFromDryRunAtFullSize.holes`, `innerCompiledVerifierSoundFromDryRunAtFullSize_dry` and their forms at the small size; `soundThreeFull_req`.

Under which hypotheses. `innerCompiledVerifierSoundFromDryRunAtFullSize_codes`, `innerCompiledVerifierSoundFromDryRunAtSmallSize_codes`: the theorem on innerCompiledVerifier at
the two sizes under the four named hypotheses `RemainingSoundnessConditionsFromDryRunAtFullSize T` | `RemainingSoundnessConditionsFromDryRunAtSmallSize T` (`keySound`,
`proofSound`, `commitment`, `sound`); no other hypothesis is a binder; the laws that are in the
types of the parameters (the head of Johnson/Flat/TwoSizes.lean names them) stay.
`soundThreeFull_ref_codes`: at the full size, at the claim on a decoded table and the reference
numbers, under the three of `LeftThreeFull T` (`keySound`, `proofSound`, `commitment`) and the
premises that fix parameters. `entrySoundFromDryRunAtFullSize_codes`, `entrySoundFromDryRunAtSmallSize_codes`: the entry
file's named hypothesis; no hypothesis is a binder.

What it does not show.
- The limits said at each theorem in its own file: none falls here but the hypothesis on codes.
- Two limits out of the head of Johnson/Flat/TwoSizes.lean, because they bear on what the four are
  worth: `G.k`, `G.c`, `G.block` are parameters; and that the guards (`GuardsPassFull`,
  `GuardsPassSmall`, Johnson/Flat/WireAt.lean) pass is shown at no G: where one fails, that file's
  hypothesis on soundness holds vacuously, and where both fail, all that is left is met by a vacuous
  value.
- nothing in this library calls the five.
- At the small size `proofSound` cannot be met by the small example's protocol at the one claim that
  is defined concretely in this library (Johnson/Flat/TwoSizes.lean): by reading, no theorem.
- The name says that the proof of the statement on codes is used, not that nothing is left to prove.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ThreeFull
import Cb.Bridge.GlCodesProved

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {G : FilesParameters X RecFull}
  {P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- `innerCompiledVerifierSoundFromDryRunAtFullSize` with the hypothesis on codes filled: four named hypotheses are left. -/
theorem innerCompiledVerifierSoundFromDryRunAtFullSize_codes {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P} (h : RemainingSoundnessConditionsFromDryRunAtFullSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  innerCompiledVerifierSoundFromDryRunAtFullSize Cb.Gl.bchks46At h

/-- `entrySoundFromDryRunAtFullSize` with the hypothesis on codes filled: no hypothesis is a binder. -/
theorem entrySoundFromDryRunAtFullSize_codes (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataFromDryRunAtFullSize T) := entrySoundFromDryRunAtFullSize Cb.Gl.bchks46At T

end

section
variable (s : Cm.Scales) (E : Coding (claimsReq (frS.toDecR frZ 402653181) numsRef s))
  (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- `soundThreeFull_ref` with the hypothesis on codes filled: three named hypotheses are left,
beside the premises that fix parameters. -/
theorem soundThreeFull_ref_codes (lawful : s.Lawful)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) (h : LeftThreeFull T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  soundThreeFull_ref s E G P Cb.Gl.bchks46At lawful T hb hn h

end

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {G : FilesParameters X RecSmall}
  {P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- `innerCompiledVerifierSoundFromDryRunAtSmallSize` with the hypothesis on codes filled: four named hypotheses are left. Of the
four, `proofSound` cannot be met by the small example's protocol at the one claim that is written in
this library: by reading, no theorem. -/
theorem innerCompiledVerifierSoundFromDryRunAtSmallSize_codes {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P} (h : RemainingSoundnessConditionsFromDryRunAtSmallSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtSmallSize T))
      (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtSmallSize T)) :=
  innerCompiledVerifierSoundFromDryRunAtSmallSize Cb.Gl.bchks46At h

/-- `entrySoundFromDryRunAtSmallSize` with the hypothesis on codes filled: no hypothesis is a binder. -/
theorem entrySoundFromDryRunAtSmallSize_codes (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataFromDryRunAtSmallSize T) := entrySoundFromDryRunAtSmallSize Cb.Gl.bchks46At T

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtFullSize_codes
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtSmallSize_codes
#print axioms VerifiableInference.OnPublicFiles.soundThreeFull_ref_codes
#print axioms VerifiableInference.OnPublicFiles.entrySoundFromDryRunAtFullSize_codes
#print axioms VerifiableInference.OnPublicFiles.entrySoundFromDryRunAtSmallSize_codes
