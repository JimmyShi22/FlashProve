-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/GameOGen.lean: index binding with an extractor that may query the hash function, from
the terms of ZKCP/Gen.lean (Johnson/Top/ArmsD.lean) to those of ZKCP/Defs.lean
(Johnson/Top/GameO.lean), and from there to the front.

Theorems with their proofs.
  `ZKCP.SpecialAny.extOfO`: an extractor of Johnson/Top/ArmsD.lean over one hash function, as one of
    Johnson/Top/GameO.lean.
  `ZKCP.SpecialAny.bindingExpO_toRom`, `bindingWithO_of_gen`: ZKCP/SpecialAny.lean's
    `bindingExp_toRom` and `bindingWith_of_gen` for such extractors: the same budget, the same
      bound.
  `VerifiableInference.Rec.CommitmentBindsOO`: Johnson/Top/SoundO.lean's `CommitmentBindsO` where
    the scheme whose verifier holds the key itself is bound in the new game already.
  `VerifiableInference.Rec.soundForWithO_systemE_O`: `soundForWithO_systemE` from that.
Limits: those of the three files named. `CommitmentBindsOO` is a hypothesis: nothing here proves it
of any code.

-/
import ZKCP.SpecialAny
import Rom.NoCoinExits
import Rom.OneOfCount
import Johnson.Top.ArmsD
import Johnson.Top.SoundO

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace ZKCP.SpecialAny

open Rom (rom toRom ofRom trTo trOf)
open ZKCP.Special

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- An extractor over one hash function in the terms of ZKCP/Gen.lean, in those of ZKCP/Defs.lean.
-/
def extOfO (E : Gen.ExtractorO (rom lam) I X W IVK Pf) : ZKCP.ExtractorO lam I X W IVK Pf :=
  ⟨fun k tr => ofRom (E.Ei k (trTo tr)), fun k tr x π tr' => E.Ew k (trTo tr) x π (trTo tr')⟩

variable (R : IndexedRelation I X W PP)
  {G : Gen.Arg (rom lam) I X W IVK ISK Pf} {A : Arg lam I X W IVK ISK Pf} (h : Agrees G A)

include h

theorem bindingExpO_toRom {St : Type} (E : Gen.ExtractorO (rom lam) I X W IVK Pf)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    Gen.bindingExpO G E (toRom Ct) (fun st => toRom (Pt st)) =
      toRom (ZKCP.bindingExpO A (extOfO E) Ct Pt) := by
  have e : ZKCP.bindingExpO A (extOfO E) Ct Pt = Ct.withTrace.bind fun o =>
      (ofRom (E.Ei o.1.1 (trTo o.2))).bind fun iStar => (Pt o.1.2).withTrace.bind fun o' =>
        (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
          .pure ⟨b, iStar, o'.1.1, E.Ew o.1.1 (trTo o.2) o'.1.1 o'.1.2 (trTo o'.2)⟩ := rfl
  have e' : Gen.bindingExpO G E (toRom Ct) (fun st => toRom (Pt st)) =
      (toRom Ct).withTrace.bind fun o => (E.Ei o.1.1 o.2).bind fun iStar =>
        (toRom (Pt o.1.2)).withTrace.bind fun o' => (G.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
          .pure ⟨b, iStar, o'.1.1, E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ := rfl
  rw [e, e']
  simp only [h.V, Rom.toRom_bind, Rom.toRom_withTrace, Rom.toRom_pure, Rom.toRom_ofRom,
    Rom.trTo_trOf, Rom.OComp.bind_assoc, Rom.OComp.bind]

theorem bindingWithO_of_gen (E : Gen.ExtractorO (rom lam) I X W IVK Pf) (q : ℕ)
    (ε : ℕ → ℕ → ℝ≥0∞) (H : Gen.HasIndexBindingWithO (toPair R) G E q ε) :
    ZKCP.HasIndexBindingWithO R A (extOfO E) q ε := by
  refine ⟨fun k tr => ⟨Rom.queryBound_ofRom _ q (H.1 k _).1, Rom.drawsNoCoin_ofRom _ (H.1 k _).2⟩,
    ?_⟩
  intro tC tP St Ct Pt hC hP
  have := H.2 tC tP St (toRom Ct) (fun st => toRom (Pt st)) ((Rom.queryBound_toRom _ _).2 hC)
    fun st => (Rom.queryBound_toRom _ _).2 (hP st)
  rwa [bindingExpO_toRom h, Rom.Pr_toRom, bindingBad_eq] at this

end ZKCP.SpecialAny

namespace VerifiableInference.Rec
open Rom ZKCP

variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (E : ZKCP.Gen.ExtractorO (rom 256) I X Unit IVK Pf) (q₀ : ℕ) (enc : IVK → Option ZKCP.Str)
  (extO : ZKCP.ExtractorO 256 I X Unit (ZKCP.Digest 256) (IVK × Pf)) (q : ℕ)

/-- Index binding of the scheme whose verifier holds the key itself, with the extractor E, which may
query the hash function at most q₀ times, gives index binding of the scheme whose verifier holds the
hash function's answer at the key's code, with the extractor `extO` and at most q queries, at ε'. -/
def CommitmentBindsOO (IsTrue : I → X → Prop) (ε ε' : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ZKCP.HasIndexBindingWithO (ZKCP.languageRelation IsTrue) (SpecialAny.oneOf G)
      (SpecialAny.extOfO E) q₀ ε →
    ZKCP.HasIndexBindingWithO (ZKCP.languageRelation IsTrue) ((SpecialAny.oneOf G).digestKey enc)
      extO q ε'

variable (bound : ℕ) {build : List Token × List Token → List Token → Option X} (π₀ : IVK × Pf)
  (nextToken : I → List Token → Option Token)

/-- `soundForWithO_systemE` (Johnson/Top/SoundO.lean) where the scheme whose verifier holds the key
itself is bound in the new game already. -/
theorem soundForWithO_systemE_O {IsTrue : I → X → Prop} {ε ε' : ℕ → ℕ → ℝ≥0∞} {ε'' : ℕ → ℝ≥0∞}
    (hb : ZKCP.Gen.HasIndexBindingWithO (ZKCP.Special.toPair (ZKCP.languageRelation IsTrue)) G E q₀
      ε)
    (hV : ∀ k x π, (G.V k x π).NoCoin) (hc : CommitmentBindsOO G E q₀ enc extO q IsTrue ε ε')
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2)
    (hε : ∀ tC tP, ε' tC tP ≤ ε'' (tC + tP)) :
    SoundForWithO (tokenArgumentSystem G enc bound build π₀ nextToken)
      (fun c l => deterministicOf (extO.Ei c l)) q claim ε'' :=
  soundForWithO_ofArgument (tokenScheme G enc bound build π₀) (commitE G enc bound) nextToken
    (ZKCP.drawsNoCoin_buildInstance_V _ _ _ _
      (ZKCP.drawsNoCoin_verifyDigestKey enc fun k x π => drawsNoCoin_ofRom _ (hV k x π)))
    claim extO.buildInstance q ε' ε''
    (ZKCP.HasIndexBindingWithO.buildInstance x₀ sound
      (ZKCP.HasIndexBindingWithO.of_sameV rfl
        (hc (ZKCP.SpecialAny.bindingWithO_of_gen (ZKCP.languageRelation IsTrue)
          (ZKCP.SpecialAny.agrees_oneOf G) E q₀ ε hb))))
    hε

end VerifiableInference.Rec

#print axioms ZKCP.SpecialAny.bindingWithO_of_gen
#print axioms VerifiableInference.Rec.soundForWithO_systemE_O
