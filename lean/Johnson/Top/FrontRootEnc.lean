-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontRootEnc.lean: the front's soundness for the verifier with a record, the key being
(root, record) and the key's code an argument.

One statement with its proof.
Main names:
  `soundForWith_rootSystemE`: the statement of `soundForWith_recSystemE`
    (Johnson/Top/FrontEnc.lean) with `VR`, `KeyRoot`, `PrfRoot`, `indexExtractorAtRootAndOutOfDomainSample`
    (Johnson/RecCompile/FrontRoot.lean): for a one-to-one `enc : KeyRoot 256 L → Option ZKCP.Str`
    the 256-bit commitment is the hash function's answer at the code of (root, record).
Limits: under what `soundForWith_recSystemE` has. It does not say that a written `enc` is that of
any program, and nothing on completeness.

-/
import Johnson.Top.FrontEnc
import Johnson.RecCompile.FrontRoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Rec
open Rom ZKCP Iop Compile Compile.Batch Compile.Batch.Cms

variable {I X ISK : Type} {L : HolographicProtocol I X}

theorem soundForWith_rootSystemE (W : QueryLayout 256 L.carrierC) (Sd : OutOfDomainSampleQueryLayout 256 W.K L) (p : Params)
    (m : OracleCoding (spec 256 W.K L.carrierC) 256) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1)
    (A : ZKCP.Gen.Arg (spec 256 W.K L.carrierC) I X Unit (KeyRoot 256 L) ISK (PrfRoot 256 L))
    (hA : A.V = VR W Sd p) (enc : KeyRoot 256 L → Option ZKCP.Str)
    (inj : ZKCP.CodeIsOneToOne enc) (bound : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : KeyRoot 256 L × PrfRoot 256 L)
    (nextToken : I → List Token → Option Token) {Yes IsTrue : I → X → Prop}
    (sub : ∀ i x, Yes i x → IsTrue i x) {ε : ℕ → ℕ → ℝ≥0∞} {ε' : ℕ → ℝ≥0∞}
    (bnd : ZKCP.Gen.HasIndexBindingWith (relPair Yes IsTrue sub) A (indexExtractorAtRootAndOutOfDomainSample W) ε)
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ε' (tC + tP)) :
    SoundForWith (tokenArgumentSystem (schemeOverOneHashFunction m A) enc bound build π₀ nextToken)
      (tokenExtractorE (X := X) (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)) enc).Ei claim ε' :=
  soundForWith_systemE (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)) enc bound π₀ nextToken inj
    (IsTrue := IsTrue)
    (bindingR_one W m hl hn (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) A ε
      (fun tC tP St Ct Pt hC hP => bnd tC tP St Ct Pt hC hP))
    (fun k x π => noCoin_overOne m _ (by
      rw [hA]
      exact noCoin_of_detBound _ _ (detBound_VR W Sd p k x π)))
    claim x₀ sound hε

end VerifiableInference.Rec

#print axioms VerifiableInference.Rec.soundForWith_rootSystemE
