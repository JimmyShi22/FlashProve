-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/WholeKey/CompleteOneHash.lean: COMPLETENESS OF THE SCHEME WITH THE WHOLE KEY OVER ONE HASH
FUNCTION, IN THE DEFINITION's OWN FORM (ZKCP.HasCompletenessError, ZKCP/Defs.lean),
at an input r and an honest side h: from complete_argW (Johnson/WholeKey/Complete.lean), by the two
roads upward that Johnson/Prover/All/AtScheme.lean takes at the older key: the library's exit
(completeness_overOne) and the exit by the hash function's first input block (completeness_overOneF,
Rom/OverOneF.lean). The same five premises, the same number.

Main names (namespace OnBytes.WholeKey).
  complete_argW_oneHash   at wholeOne r h (Johnson/WholeKey/AtInput.lean).
  factors_proveAt, factors_proveW   the prover factors, as its one compiled run does.
  complete_argW_oneHashF   the same by the exit by the first input block.

By: complete_argW · completeness_overOne · completeness_overOneF ·
ZKCP.SpecialAny.completeness_of_gen, agrees_oneOf · factors_proveX, factorsF_of, PassFits
(Johnson/Prover/All/CountF.lean and beneath).

Limits. Those of complete_argW: the accept laws and the sets' measures are premises; one commitment,
one request; nothing on bad keys. Nothing on wholeId (the key that begins with the commitment ID) or
on argLow. It states no goal. Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Complete
import Johnson.WholeKey.AtInput
import Johnson.Prover.All.AtScheme

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Yes : r.Index → r.Instance → Prop)
  (Bs : r.Index → r.protocol.EncodingRandomness → r.Instance → Draw 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits (h.KT × h.KL × h.KB) → Bads r.protocol)
  {ζ₁ ζ₂ δT δL δB : ℝ≥0∞}

/-- **Over one hash function, in the definition's own form**: the library's exit. -/
theorem complete_argW_oneHash (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hF : SideFit r.queryLayout r.compilerParameters h)
    (acc : AccLaws r.queryLayout r.seedQueries h.st.joint Yes Bs ζ₁ ζ₂ δT δL δB) (hS : StopsIn h.st Bs) :
    ZKCP.HasCompletenessError (ZKCP.languageRelation Yes) (wholeOne r h)
      (alphaAll r.queryLayout h.capT h.capL h.capB ζ₁ ζ₂ δT δL δB) :=
  ZKCP.SpecialAny.completeness_of_gen (ZKCP.languageRelation Yes) (ZKCP.SpecialAny.agrees_oneOf _) _
    (completeness_overOne r.oracleCoding _ _ 1 _
      (complete_argW r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters h Yes Bs hL hW hF acc hS))

/-- The prover behind its coins factors. -/
theorem factors_proveAt {hK : 0 < r.queryLayout.K} {pass : Pass 256 (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)}
    (H : PassFits r.queryLayout r.seedQueries hK pass) (isk : Isk 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (x : r.Instance)
    (d : DrawP 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KB) :
    (proveAt r.queryLayout r.answerCode r.fixedSample h isk x d).FactorsBy (agP hK pass) := by
  unfold proveAt
  split
  · trivial
  · exact OComp.FactorsBy.bind (factors_proveX hK pass Tag.onl r.protocol.onlineBatch (wBC r.queryLayout) r.queryLayout.embB id _ _ _ _
      _ _ _ _ H.testsB) fun _ => trivial

/-- The prover with its coins factors. -/
theorem factors_proveW {hK : 0 < r.queryLayout.K} {pass : Pass 256 (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)}
    (H : PassFits r.queryLayout r.seedQueries hK pass) (isk : Isk 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) :
    ∀ b : List (r.Instance × Unit), (proveW r.queryLayout r.answerCode r.fixedSample h isk b).FactorsBy (agP hK pass)
  | [] => trivial
  | [(x, _)] => fun a b c =>
    (show Rom.OComp.FactorsBy (agP hK pass)
      ((proveAt r.queryLayout r.answerCode r.fixedSample h isk x ⟨a.val, h.kB.e b, h.coB.e c⟩).bind fun π =>
        (.pure ⟨[π], rfl⟩ : Rom.OComp _ (ZKCP.Gen.Slots (RequestProof 256 r.protocol) [(x, ())]))) from
      OComp.FactorsBy.bind (factors_proveAt r h H isk x _) fun _ => trivial)
  | _ :: _ :: _ => trivial

/-- **The same by the exit by the hash function's first input block.** -/
theorem complete_argW_oneHashF {hK : 0 < r.queryLayout.K}
    {pass : Pass 256 (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)} (F : FirstIs hK r.oracleCoding)
    (H : PassFits r.queryLayout r.seedQueries hK pass) (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hF : SideFit r.queryLayout r.compilerParameters h)
    (acc : AccLaws r.queryLayout r.seedQueries h.st.joint Yes Bs ζ₁ ζ₂ δT δL δB) (hS : StopsIn h.st Bs) :
    ZKCP.HasCompletenessError (ZKCP.languageRelation Yes)
      (ZKCP.SpecialAny.oneOf (overOneArgF r.oracleCoding (moreP pass) (wholeKeySchemeOverTypedOracles r h)))
      (alphaAll r.queryLayout h.capT h.capL h.capB ζ₁ ζ₂ δT δL δB) :=
  ZKCP.SpecialAny.completeness_of_gen (ZKCP.languageRelation Yes) (ZKCP.SpecialAny.agrees_oneOf _) _
    (completeness_overOneF r.oracleCoding (moreP pass) _ _ 1 _
      (fun k b => factorsF_of hK pass r.oracleCoding F (factors_proveW r h H k b))
      (complete_argW r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters h Yes Bs hL hW hF acc hS))

end OnBytes.WholeKey
