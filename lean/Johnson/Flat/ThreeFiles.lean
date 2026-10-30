-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ThreeFiles.lean: the theorem on innerCompiledVerifier at the full size
(Where this and lean/THEOREM.md differ, the page
holds.) with "sound" paid
(Johnson/Flat/ThreeFull.lean), still under three named hypotheses and the theorem on codes, at the
table of scales that is read off the scale file and the parameter file: the table has a name, and
that it is lawful is no premise.

One theorem.
  soundThreeFull_files: if scalesOfFiles policy KL (Johnson/Flat/ScalesOf.lean) returns s: the
    statement of soundThreeFull_ref at that s, under the three named hypotheses, the theorem on
    codes, T's builder buildReq and T's model nextTok s. By scalesOfFiles_lawful.
That this s is the table of the words which the verifier's own reader lays into its public part is
not shown here.

Limits: those of Johnson/Flat/ThreeFull.lean, but for the table of scales. The letter G (the key
file's and the proof file's data) is still tied to nothing: that it is made at the same two files is
not asked here, and where it is made at others "proofSound" cannot be expected to hold.

-/
import Johnson.Flat.ScalesOf
import Johnson.Flat.ThreeFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model

section
variable (s : Cm.Scales) (E : Coding (claimsReq (frS.toDecR frZ 402653181) numsRef s))
  (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **Under the three named hypotheses LeftThreeFull T and the theorem on codes** (hypotheses of the
theorem: Lean's list of axioms does not show them), where scalesOfFiles returns s, at T's builder
buildReq and T's model nextTok s: the theorem on innerCompiledVerifier at the full size
(Where this and lean/THEOREM.md differ, the page
holds.), at the table of
scales of the two files. -/
theorem soundThreeFull_files {policy KL : ByteArray} (hs : scalesOfFiles policy KL = .ok s)
    (hA : BCHKS46At GF GE)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) (h : LeftThreeFull T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  soundThreeFull_ref s E G P hA (scalesOfFiles_lawful hs) T hb hn h

end

end VerifiableInference.OnPublicFiles
