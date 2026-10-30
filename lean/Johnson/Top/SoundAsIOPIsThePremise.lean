-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SoundAsIOPIsThePremise.lean: FOR EVERY INPUT OF THE COMPILER: soundness as an IOP
(HolographicProtocol.IndexKnowledgeSoundIOP, Hiop/SoundAsIOP.lean) of the input's object IS the compiler's theorem's four
hypotheses on the object's soundness, together with a true count of the points with a collision.

Why. At the public files the four hypotheses are theorems, so there an implication "soundness as an
IOP gives them" could be proved by throwing its premise away, and its statement shows nothing. Here the
input is any: of a general input nothing is known, so the statement itself says what the premise of the
compiler's theorem is.

  Spec.indexKnowledgeSoundIOP_iff_premises, indexKnowledgeSoundIOP_iff_premises: for every r : InnerCompilerInput and
    b : SoundnessAnalysisData r whose type of witnesses has the one element w₀:
      r.protocol.IndexKnowledgeSoundIOP (fun i x => b.Rno i x w₀) r.offlineRoundSplits (2 ^ r.queryLayout.depthReqT) r.linkRoundSplits
        (2 ^ r.queryLayout.depthReqL) b.εs
    holds if and only if CompilerSoundnessConditionStatements.noneColl, CompilerSoundnessConditionStatements.keySound b, CompilerSoundnessConditionStatements.entrySound b,
    CompilerSoundnessConditionStatements.proofSound b (Johnson/Top/InnerCompiledVerifier.lean) hold, and for some number eR that is at most
    b.εs of all points every table has a collision at no more than eR points.

  argumentExtractor_is_extractIndex: the index extractor of the compiled scheme WHOSE VERIFIER HOLDS THE
    KEY (root, sample) is the IOP's: at every input, indexExtractorAtRootAndOutOfDomainSample (Johnson/TypedOracleCompiler/RecCompile/FrontRoot.lean;
    it stands in CompilerSoundnessConditionStatements.commitment and CompilerSoundnessConditions.binds) at a key and a query log is extractIndex at the
    table that the log determines under the root, and the key's sample. By definition. The extractor of
    the system whose verifier holds the commitment stands behind that one (SoundnessAnalysisData.ext, tied to it by
    CompilerSoundnessConditionStatements.commitment): of it nothing is said here.

Limits. The last clause is no hypothesis of the compiler's theorem: that theorem asks instead a law on
the point as it is made from hash answers (CompilerSoundnessConditionStatements.seedLaw), and fills the library's clause on the
count with the number of all points (CompilerSoundnessConditions.binds). So soundness as an IOP asks MORE of the object
than the compiler's theorem does, by that clause, and gives nothing of seedLaw. The other ten of the
fifteen hypotheses (what the verifiers read, the marks, the wires, the codes, the commitment) are no
matter of soundness of the IOP and are not touched. One element in the type of witnesses: as at the
protocol's description; with more, proofSound says more than IndexKnowledgeSoundIOP (it names a witness
map).
-/
import Hiop.SoundAsIOPProofs
import Johnson.Top.InnerCompiledVerifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Prob
open _root_.Iop (soundInParts_iff_soundAtR sndBKT_conseq)
open TypedOracleCompiler.Compile.Batch (extEnc)
open TypedOracleCompiler.Compile.Batch.Cms (KeyRoot indexExtractorAtRootAndOutOfDomainSample)

namespace Spec

/-- States: **soundness as an IOP is the compiler's four hypotheses on soundness and a true count of
the points with a collision**, at every input. -/
def indexKnowledgeSoundIOP_iff_premises : Prop :=
  ∀ (r : InnerCompilerInput) (b : SoundnessAnalysisData r) (w₀ : b.Wn), (∀ w : b.Wn, w = w₀) →
    (r.protocol.IndexKnowledgeSoundIOP (fun i x => b.Rno i x w₀) r.offlineRoundSplits (2 ^ r.queryLayout.depthReqT) r.linkRoundSplits
        (2 ^ r.queryLayout.depthReqL) b.εs ↔
      CompilerSoundnessConditionStatements.noneColl (r := r) ∧ CompilerSoundnessConditionStatements.keySound b ∧ CompilerSoundnessConditionStatements.entrySound b ∧
        CompilerSoundnessConditionStatements.proofSound b ∧
        ∃ eR : ℕ, (eR : ℝ≥0∞) ≤ b.εs * (Fintype.card r.protocol.OutOfDomainSeed : ℝ≥0∞) ∧
          ∀ table : r.protocol.Table, cnt (fun point => r.protocol.hasCollisionAt table point) ≤ eR)

end Spec

theorem indexKnowledgeSoundIOP_iff_premises : Spec.indexKnowledgeSoundIOP_iff_premises := by
  intro r b w₀ one
  constructor
  · rintro ⟨errors, within, parts⟩
    have S := (soundInParts_iff_soundAtR _ _ _ _ _).1 parts
    refine ⟨S.noneColl, ⟨errors.offline, within.offline, S.sndT⟩,
      ⟨errors.link, within.link, S.sndL⟩,
      ⟨fun _ _ _ => w₀, errors.online, within.online, fun rec => ?_⟩,
      ⟨errors.samplePoint, within.samplePoint, S.rcd⟩⟩
    exact sndBKT_conseq _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ h => h) (S.sndB rec)
  · rintro ⟨hN, ⟨εT, bT, sT⟩, ⟨εL, bL, sL⟩, ⟨wit, εB, bB, sB⟩, ⟨eR, bR, hR⟩⟩
    refine ⟨⟨eR, εT, εL, εB⟩, ⟨bR, bT, bL, bB⟩, (soundInParts_iff_soundAtR _ _ _ _ _).2
      ⟨hN, hR, sT, sL, fun rec => ?_⟩⟩
    refine sndBKT_conseq _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x y τ _ h => ?_) (sB rec)
    rw [one (wit (x, rec) y τ)] at h
    exact h

/-- **The index extractor of the compiled scheme whose verifier holds the key is the IOP's
extractor**, at the table that the query log determines under the key's root, and the key's
out-of-domain sample. -/
theorem argumentExtractor_is_extractIndex (r : InnerCompilerInput) (key : KeyRoot 256 r.protocol) (log : _) :
    (indexExtractorAtRootAndOutOfDomainSample r.queryLayout).Ei key log = r.protocol.extractIndex (extEnc r.queryLayout log key.cm) key.rcd := rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.indexKnowledgeSoundIOP_iff_premises
#print axioms VerifiableInference.OnPublicFiles.argumentExtractor_is_extractIndex
