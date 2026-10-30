-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontCommit.lean: the steps of Johnson/Top/FrontEnc.lean with the step from the key to
the commitment as a hypothesis.

One definition and two theorems with their proofs, for any scheme over one hash function.
`soundForWith_systemE` (Johnson/Top/FrontEnc.lean) passes from the scheme whose verifier holds the
key to the scheme whose verifier holds the hash function's answer at the key's code by
`HasIndexBindingWith.digestKey`, which asks that no two keys have the same code and names the
library's extractor. Here that one step is a hypothesis, with any extractor and any cost.
Main names (namespace `VerifiableInference.Rec`):
  `CommitmentBinds G E enc ext IsTrue ε εId`: index binding of G with E at ε gives index binding of
    G behind the digest of `enc`, with `ext`, at ε tC tP + εId (tC + tP).
  `commitmentBinds_of_code`: it holds at a code under which no two keys agree, at the library's
    extractor and cost.
  `soundForWith_systemE_ext`: `SoundForWith` for `tokenArgumentSystem G enc …` with the extractor made from
    `ext`.
Limits: as in Johnson/Top/FrontEnc.lean. `CommitmentBinds` is a statement on every committer and
every prover; where the code is not one to one this library does not prove it.

-/
import Johnson.Top.FrontEnc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Rec
open Rom ZKCP

variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (E : ZKCP.Gen.Extractor (rom 256) I X Unit IVK Pf) (enc : IVK → Option ZKCP.Str)
  (ext : ZKCP.Extractor 256 I X Unit (ZKCP.Digest 256) (IVK × Pf))

/-- Index binding of the scheme whose verifier holds the key itself gives index binding of the
scheme whose verifier holds the hash function's answer at the key's code, with the extractor `ext`,
at the cost of `εId (tC + tP)`. -/
def CommitmentBinds (IsTrue : I → X → Prop) (ε : ℕ → ℕ → ℝ≥0∞) (εId : ℕ → ℝ≥0∞) : Prop :=
  ZKCP.HasIndexBindingWith (ZKCP.languageRelation IsTrue) (SpecialAny.oneOf G) (Special.extOf E) ε →
    ZKCP.HasIndexBindingWith (ZKCP.languageRelation IsTrue) ((SpecialAny.oneOf G).digestKey enc) ext
      fun tC tP => ε tC tP + εId (tC + tP)

/-- A code under which no two keys agree gives `CommitmentBinds`, at the library's extractor and
cost. -/
theorem commitmentBinds_of_code (h : ZKCP.CodeIsOneToOne enc) (IsTrue : I → X → Prop)
    (ε : ℕ → ℕ → ℝ≥0∞) :
    CommitmentBinds G E enc ((Special.extOf E).digestKey enc) IsTrue ε
      fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  fun hb => hb.digestKey h

variable (bound : ℕ) {build : List Token × List Token → List Token → Option X} (π₀ : IVK × Pf)
  (nextToken : I → List Token → Option Token)

/-- `soundForWith_systemE` with `CommitmentBinds` where that theorem calls
`HasIndexBindingWith.digestKey`. -/
theorem soundForWith_systemE_ext {IsTrue : I → X → Prop} {ε : ℕ → ℕ → ℝ≥0∞} {εId ε' : ℕ → ℝ≥0∞}
    (hb : ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) G E ε)
    (hV : ∀ k x π, (G.V k x π).NoCoin) (hc : CommitmentBinds G E enc ext IsTrue ε εId)
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε tC tP + εId (tC + tP) ≤ ε' (tC + tP)) :
    SoundForWith (tokenArgumentSystem G enc bound build π₀ nextToken)
      (ext.buildInstance : ZKCP.Extractor 256 I (List Token × List Token) Unit (ZKCP.Digest 256)
        (List Token × (IVK × Pf))).Ei claim ε' :=
  soundForWith_ofArgument (tokenScheme G enc bound build π₀) (commitE G enc bound) nextToken
    (ZKCP.drawsNoCoin_buildInstance_V _ _ _ _
      (ZKCP.drawsNoCoin_verifyDigestKey enc fun k x π => drawsNoCoin_ofRom _ (hV k x π)))
    claim ext.buildInstance (fun tC tP => ε tC tP + εId (tC + tP)) ε'
    (ZKCP.HasIndexBindingWith.buildInstance x₀ sound
      ((ZKCP.hasIndexBindingWith_coinsFirst_iff bound _ _).2
        (hc (ZKCP.SpecialAny.bindingWith_of_gen (ZKCP.languageRelation IsTrue)
          (ZKCP.SpecialAny.agrees_oneOf G) (ZKCP.Special.extOf E) ε
          (by rw [ZKCP.Special.extTo_extOf]; exact hb)))))
    hε

end VerifiableInference.Rec

#print axioms VerifiableInference.Rec.commitmentBinds_of_code
#print axioms VerifiableInference.Rec.soundForWith_systemE_ext
