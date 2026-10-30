-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/Front.lean: THE FRONT's SOUNDNESS STATEMENT (SoundForWith,
VerifiableInference/MoreStatements.lean) FOR AN ARGUMENT SYSTEM WHOSE SCHEME IS ANY SCHEME OVER ONE
HASH FUNCTION, and then for every scheme whose verifier is VC (Cms.lean), the compiled verifier with
a record.
The steps are generic in the scheme's types and are used as they stand:

SpecialAny.oneOf (a scheme over rom 256 in the form of ZKCP/Defs.lean), Arg.digestKey (the key
becomes the hash function's answer at the key's code under a tag; the key travels with each proof),
Arg.coinsFirst, Arg.buildInstance (an instance is a prompt with output tokens),
ArgumentSystem.ofArgument. No fixWitness: the relation has no witness here.
  systemOf G .. : the argument system; soundForWith_systemOf: from index binding of G for the
    language IsTrue, at ε, with a verifier that samples nothing and countably many keys.
  soundForWith_recSystem: the same at G := schemeOverOneHashFunction m A for every A with A.V = VC W Sd p, the
    extractor extractorOverOneHashFunction m (extractorC0 W); its hypothesis «bound» is index binding
    of A over the typed oracles (what join_all | glW_rec_binds_recIx | val9_binds conclude).
The 256-bit commitment is the digest of the WHOLE key FullKey (root, record, offline string, further
roots with their records and links).
NOT HERE: completeness, zero knowledge, extraction of the honest index (they ask a committer and a
prover); build, claim, nextToken are letters.
The number «bound» from which the committer's coins are drawn is a letter too: soundness asks
nothing of the committer.

-/
import Johnson.RecCompile.One
import VerifiableInference.OfArgument
import VerifiableInference.KeyCode
import Compile.DigestKeyBinding
import ZKCP.CoinsFirstArg
import ZKCP.BuildInstance
import ZKCP.SpecialAny
import Rom.NoCoinExits

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Rom

theorem noCoin_of_detBound {S : OSpec} {α : Type} :
    ∀ (c : OComp S α) (t : ℕ), Compile.DetBound c t → c.NoCoin
  | .pure _, _, _ => trivial
  | .query _ _ _, 0, h => h.elim
  | .query _ _ k, t + 1, h => fun r => noCoin_of_detBound (k r) t (h r)
  | .sample _ _, _, h => h.elim

end Rom

namespace VerifiableInference.Rec
open Rom ZKCP

section Gen
variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (E : ZKCP.Gen.Extractor (rom 256) I X Unit IVK Pf) (hK : Countable IVK) (tag bound : ℕ)
  (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)
  (nextToken : I → List Token → Option Token)

/-- The scheme with the digest of its key for a key. -/
def digestSchemeOf := (ZKCP.SpecialAny.oneOf G).digestKey (codeUnderTag tag hK)

/-- The scheme on prompts with output tokens. -/
def tokenSchemeOf : ZKCP.Arg 256 I (List Token × List Token) Unit (ZKCP.Digest 256)
    (I × Fin (bound + 1)) (List Token × (IVK × Pf)) :=
  ((digestSchemeOf G hK tag).coinsFirst bound).buildInstance build (fun _ => []) π₀

def commitOfG (i : I) (coins : Fin (bound + 1)) : ZKCP.OComp 256 (ZKCP.Digest 256) :=
  (((digestSchemeOf G hK tag).C i).withCoins coins.val).mapO Prod.fst

def tokenExtractorOf : ZKCP.Extractor 256 I (List Token × List Token) Unit (ZKCP.Digest 256)
    (List Token × (IVK × Pf)) :=
  ((ZKCP.Special.extOf E).digestKey (codeUnderTag tag hK)).buildInstance

/-- The argument system. -/
def systemOf : ArgumentSystem :=
  ArgumentSystem.ofArgument (tokenSchemeOf G hK tag bound build π₀) (commitOfG G hK tag bound)
    nextToken

variable {build}

/-- Soundness for a claim, with the extractor named. This is said under the hypotheses that stand in
the statement itself, which this comment does not list; it is no claim that they hold. -/
theorem soundForWith_systemOf {IsTrue : I → X → Prop} {ε : ℕ → ℕ → ℝ≥0∞} {ε' : ℕ → ℝ≥0∞}
    (hb : ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) G E ε)
    (hV : ∀ k x π, (G.V k x π).NoCoin)
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ε' (tC + tP)) :
    SoundForWith (systemOf G hK tag bound build π₀ nextToken)
      (tokenExtractorOf (X := X) E hK tag).Ei claim ε' :=
  soundForWith_ofArgument (tokenSchemeOf G hK tag bound build π₀) (commitOfG G hK tag bound)
    nextToken
    (ZKCP.drawsNoCoin_buildInstance_V _ _ _ _
      (ZKCP.drawsNoCoin_verifyDigestKey (codeUnderTag tag hK)
        fun k x π => drawsNoCoin_ofRom _ (hV k x π)))
    claim (tokenExtractorOf E hK tag)
    (fun tC tP => ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) ε'
    (ZKCP.HasIndexBindingWith.buildInstance x₀ sound
      ((ZKCP.hasIndexBindingWith_coinsFirst_iff bound _ _).2
        ((ZKCP.SpecialAny.bindingWith_of_gen (ZKCP.languageRelation IsTrue)
          (ZKCP.SpecialAny.agrees_oneOf G) (ZKCP.Special.extOf E) ε
          (by rw [ZKCP.Special.extTo_extOf]; exact hb)).digestKey
          (codeUnderTag_oneToOne tag hK))))
    hε

end Gen

section Rec
open Iop Compile Compile.Batch Compile.Batch.Cms

variable {I X ISK : Type} {L : HolographicProtocol I X}

/-- THE FRONT's SOUNDNESS FOR THE VERIFIER WITH A RECORD. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
theorem soundForWith_recSystem (W : QueryLayout 256 L.carrierC) (Sd : OutOfDomainSampleQueryLayout 256 W.K L) (p : Params)
    (m : OracleCoding (spec 256 W.K L.carrierC) 256) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1)
    (A : ZKCP.Gen.Arg (spec 256 W.K L.carrierC) I X Unit (FullKey 256 L) ISK (RequestProof 256 L))
    (hA : A.V = VC W Sd p) (hK : Countable (FullKey 256 L)) (tag bound : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : FullKey 256 L × RequestProof 256 L)
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

end Rec
end VerifiableInference.Rec

#print axioms VerifiableInference.Rec.soundForWith_systemOf
#print axioms VerifiableInference.Rec.soundForWith_recSystem
