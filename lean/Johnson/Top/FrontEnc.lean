-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontEnc.lean: the steps of Johnson/RecCompile/Front.lean with the code of a key as an
argument.

Definitions and two theorems with their proofs. In Johnson/RecCompile/Front.lean the code of a key
is `codeUnderTag tag hK`, which is picked by choice (`VerifiableInference.numberOf`) and writes a
number in unary. The soundness proof asks of the code one thing: that no two keys have the same
code. Here the code is `enc : IVK → Option ZKCP.Str`, with `inj : ZKCP.CodeIsOneToOne enc`.
Main names (namespace `VerifiableInference.Rec`):
  `digestKeyScheme`, `tokenScheme`, `commitE`, `tokenArgumentSystem`: the scheme with the digest of its key for
    a key; the scheme on prompts with output tokens; the committer's digest; the argument system.
    These four stand under no `noncomputable`.
  `tokenExtractorE`: the named extractor.
  `systemOf_eq`, `tokenExtractorOf_eq`: those of Johnson/RecCompile/Front.lean are these at
    `codeUnderTag tag hK`.
  `soundForWith_systemE`: `SoundForWith` for the system made from any scheme over one hash function.
  `soundForWith_recSystemE`: the same for every scheme whose verifier is `VC W Sd p`.
Limits: as in Johnson/RecCompile/Front.lean. Does not say: completeness; zero knowledge; that the
extractor returns an honest committer's index; that a written code is a program's own.

-/
import Johnson.RecCompile.FrontKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Rec
open Rom ZKCP

section Gen
variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (E : ZKCP.Gen.Extractor (rom 256) I X Unit IVK Pf) (enc : IVK → Option ZKCP.Str) (bound : ℕ)
  (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)
  (nextToken : I → List Token → Option Token)

def digestKeyScheme := (ZKCP.SpecialAny.oneOf G).digestKey enc

def tokenScheme : ZKCP.Arg 256 I (List Token × List Token) Unit (ZKCP.Digest 256)
    (I × Fin (bound + 1)) (List Token × (IVK × Pf)) :=
  ((digestKeyScheme G enc).coinsFirst bound).buildInstance build (fun _ => []) π₀

def commitE (i : I) (coins : Fin (bound + 1)) : ZKCP.OComp 256 (ZKCP.Digest 256) :=
  (((digestKeyScheme G enc).C i).withCoins coins.val).mapO Prod.fst

noncomputable def tokenExtractorE : ZKCP.Extractor 256 I (List Token × List Token) Unit
    (ZKCP.Digest 256) (List Token × (IVK × Pf)) :=
  ((ZKCP.Special.extOf E).digestKey enc).buildInstance

/-- The argument system, the key's code an argument. -/
def tokenArgumentSystem : ArgumentSystem :=
  ArgumentSystem.ofArgument (tokenScheme G enc bound build π₀) (commitE G enc bound) nextToken

/-- Front.lean's system is this one at the chosen code. -/
theorem systemOf_eq (hK : Countable IVK) (tag : ℕ) :
    systemOf G hK tag bound build π₀ nextToken =
      tokenArgumentSystem G (codeUnderTag tag hK) bound build π₀ nextToken := rfl

theorem tokenExtractorOf_eq (hK : Countable IVK) (tag : ℕ) :
    tokenExtractorOf (X := X) E hK tag = tokenExtractorE (X := X) E (codeUnderTag tag hK) := rfl

variable {build}

theorem soundForWith_systemE (inj : ZKCP.CodeIsOneToOne enc) {IsTrue : I → X → Prop}
    {ε : ℕ → ℕ → ℝ≥0∞} {ε' : ℕ → ℝ≥0∞}
    (hb : ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) G E ε)
    (hV : ∀ k x π, (G.V k x π).NoCoin)
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ε' (tC + tP)) :
    SoundForWith (tokenArgumentSystem G enc bound build π₀ nextToken) (tokenExtractorE (X := X) E enc).Ei claim
      ε' :=
  soundForWith_ofArgument (tokenScheme G enc bound build π₀) (commitE G enc bound)
    nextToken
    (ZKCP.drawsNoCoin_buildInstance_V _ _ _ _
      (ZKCP.drawsNoCoin_verifyDigestKey enc fun k x π => drawsNoCoin_ofRom _ (hV k x π)))
    claim (tokenExtractorE E enc)
    (fun tC tP => ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) ε'
    (ZKCP.HasIndexBindingWith.buildInstance x₀ sound
      ((ZKCP.hasIndexBindingWith_coinsFirst_iff bound _ _).2
        ((ZKCP.SpecialAny.bindingWith_of_gen (ZKCP.languageRelation IsTrue)
          (ZKCP.SpecialAny.agrees_oneOf G) (ZKCP.Special.extOf E) ε
          (by rw [ZKCP.Special.extTo_extOf]; exact hb)).digestKey inj)))
    hε

end Gen

section Rec
open Iop Compile Compile.Batch Compile.Batch.Cms

variable {I X ISK : Type} {L : HolographicProtocol I X}

/-- The front's soundness for the verifier with a record, the key's code an argument. This is said
under the hypotheses that stand in the statement itself, which this comment does not list; it is no
claim that they hold. -/
theorem soundForWith_recSystemE (W : QueryLayout 256 L.carrierC) (Sd : OutOfDomainSampleQueryLayout 256 W.K L) (p : Params)
    (m : OracleCoding (spec 256 W.K L.carrierC) 256) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1)
    (A : ZKCP.Gen.Arg (spec 256 W.K L.carrierC) I X Unit (FullKey 256 L) ISK (RequestProof 256 L))
    (hA : A.V = VC W Sd p) (enc : FullKey 256 L → Option ZKCP.Str) (inj : ZKCP.CodeIsOneToOne enc)
    (bound : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : FullKey 256 L × RequestProof 256 L)
    (nextToken : I → List Token → Option Token) {Yes IsTrue : I → X → Prop}
    (sub : ∀ i x, Yes i x → IsTrue i x) {ε : ℕ → ℕ → ℝ≥0∞} {ε' : ℕ → ℝ≥0∞}
    (bnd : ZKCP.Gen.HasIndexBindingWith (relPair Yes IsTrue sub) A (extractorC0 W) ε)
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ε' (tC + tP)) :
    SoundForWith (tokenArgumentSystem (schemeOverOneHashFunction m A) enc bound build π₀ nextToken)
      (tokenExtractorE (X := X) (extractorOverOneHashFunction m (extractorC0 W)) enc).Ei claim ε' :=
  soundForWith_systemE (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (extractorC0 W)) enc bound π₀ nextToken inj
    (IsTrue := IsTrue)
    (binding_one W m hl hn (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) A ε
      (fun tC tP St Ct Pt hC hP => bnd tC tP St Ct Pt hC hP))
    (fun k x π => noCoin_overOne m _ (by
      rw [hA]
      exact noCoin_of_detBound _ _ (detBound_VC W Sd p k x π)))
    claim x₀ sound hε

end Rec
end VerifiableInference.Rec

#print axioms VerifiableInference.Rec.soundForWith_systemE
#print axioms VerifiableInference.Rec.soundForWith_recSystemE
