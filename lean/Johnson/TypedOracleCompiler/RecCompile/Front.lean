-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/Front.lean: the front's soundness statement (`SoundForWith`,
VerifiableInference/MoreStatements.lean) for every scheme whose verifier is `VC` of this folder
(Cms.lean), the compiled verifier with a record over the second form of the compiler's verifier
side.

After lean/Johnson/RecCompile/Front.lean. That file's general part (`systemOf`,
`soundForWith_systemOf`: any scheme over one hash function) is used as it lies. Here is its last
theorem, `soundForWith_recSystem`, in that file's words. Its hypothesis `bnd` is index binding of A
over the typed oracles (CmsGlue.lean: `cms_binding_lang`).

Limits: soundness alone. No completeness, nothing on hiding, no extraction of the honest index. The
256-bit commitment of `systemOf` is the digest of the whole key under a code that is picked by
choice from countability (FrontKey.lean): it is not the programs' commitment ID, and no run can
compute it. `build`, `claim`, `nextToken` and `bound` are letters.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.One
import Johnson.RecCompile.Front

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.VerifiableInference.Rec
open Rom ZKCP _root_.VerifiableInference _root_.VerifiableInference.Rec
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X ISK : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits
                              L.link.shape}

/-- The front's soundness for the verifier with a record. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
theorem soundForWith_recSystem (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (Sd : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
    (p : Params)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) 256) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1)
    (A : ZKCP.Gen.Arg (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey 256 L aT aL) ISK (RequestProof 256
                                  L))
    (hA : A.V = VC W Sd p) (hK : Countable (FullKey 256 L aT aL)) (tag bound : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : FullKey 256 L aT aL × RequestProof 256 L)
    (nextToken : I → List Token → Option Token) {Yes IsTrue : I → X → Prop}
    (sub : ∀ i x, Yes i x → IsTrue i x) {ε : ℕ → ℕ → ℝ≥0∞} {ε' : ℕ → ℝ≥0∞}
    (bnd : ZKCP.Gen.HasIndexBindingWith (relPair Yes IsTrue sub) A (extractorC0 W) ε)
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ε' (tC + tP)) :
    SoundForWith (systemOf (schemeOverOneHashFunction m A) hK tag bound build π₀ nextToken)
      (tokenExtractorOf (X := X) (extractorOverOneHashFunction m (extractorC0 W)) hK tag).Ei claim ε' :=
  soundForWith_systemOf (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (extractorC0 W)) hK tag bound π₀ nextToken
    (IsTrue := IsTrue)
    (binding_one W m hl hn (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) A ε
      (fun tC tP St Ct Pt hC hP => bnd tC tP St Ct Pt hC hP))
    (fun k x π => noCoin_overOne m _ (by
      rw [hA]
      exact noCoin_of_detBound _ _ (detBound_VC W Sd p k x π)))
    claim x₀ sound hε

end TypedOracleCompiler.VerifiableInference.Rec
