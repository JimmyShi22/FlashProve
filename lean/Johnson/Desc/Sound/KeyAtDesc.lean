-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyAtDesc.lean: THE KEY FILE'S NAMED HYPOTHESIS ON SOUNDNESS AT A DESCRIPTION'S
OWN DECISION (`FileDescription.run`, Johnson/Desc/Block.lean), from one law for each block.

The setting. `KeySoundOfDecides` (Johnson/Desc/Sound/KeyDecides.lean) speaks of a key file whose
decision is three folds in a row, at a value `Three` that is a letter. What runs is a description's
`FileDescription.run`: the tests on the plan and on the instance, the test that every word shown is below
the prime, the three folds over the description's own blocks, the last test. Three links lie
between: the `Three` as a function of the description (`atDesc`, with `OfDesc`: its pieces hold the
description's own blocks) and "the decision's yes gives the three folds' yes" (`runGivesRowAt`):
both in Johnson/Desc/Sound/DescThree.lean and its proofs; and that the hypothesis goes over to a
decision that says yes less often (`keyCoreAnti`, Johnson/Desc/Sound/KeyCore.lean).

What is said. `KeyCoreAtDesc`, `keyCoreAtDesc`: at every description F of a key file's instances,
every three rows of pieces with `OfDesc`, and three rows of seats (`SL`) whose pieces these are:
under the premises of `KeyCoreOfDecides`, read at `atDesc F T`: `KeyCore` AT THE DECISION `F.run`.
`KeySoundAtDesc`, `keySoundAtDesc`: so `CompilerSoundnessConditionStatements.keySound` at the three protocols of `filesOf` whose
key file's decision is `F.run`, at a wire whose key file's request tree has one leaf.

Limits. A rule: no kind's law is shown here. The tests on the plan and on the instance and the last
test of the description are dropped on the way: they narrow the yes, and no premise reads them; what
a chain's end asks of its record can be kept as an invariant (`chainEnd_law_asks`,
Johnson/Desc/Sound/PassLaw.lean). That the input of the shipped theorem is such a `filesOf` is not
said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyDecides
import Johnson.Desc.Sound.DescThreeProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- **`KeyCore` at a description's own decision, from one law for each block.** -/
def KeyCoreAtDesc : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK : WholeD) (TFk TJk T3k : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (all : List LeftT) (X₁ X₂ W : Type) (F : FileDescription Kc.conf.Rec)
    (T : ThreeAt (ckP .two) (DK.at a) all F X₁ X₂ W) (J₁ J₂ Z : JK)
    (L₁ : SL (F.XiPub × F.S₁) F.Cl (frameAt (DK.at a) all (DK.at a).key₁ T.ft₁) (jWf Kc.conf) J₁)
    (L₂ : SL ((F.XiPub × F.S₁) × F.S₂) F.Cl (frameAt (DK.at a) all (DK.at a).key₂ T.ft₂) J₁ J₂)
    (L₃ : SL ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl
      (frameAt (DK.at a) all (DK.at a).key₃ T.ft₃) J₂ Z) (εs : ℝ≥0∞),
    OfDesc F T →
    T.p₁ :: T.l₁ = L₁.pieces W → T.p₂ :: T.l₂ = L₂.pieces W → T.p₃ :: T.l₃ = L₃.pieces W →
    (atDesc F T).Fits → L₁.Laws → L₂.Laws → L₃.Laws →
    (∀ rec y, L₁.rd0 ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) = (rec, y) ∧
      L₁.inv0 ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => []))) →
    (∀ b, L₂.rd0 ((b.1, F.start₂ b.1.1), b.2) = L₁.rdZ b ∧
      (L₁.invZ b → L₂.inv0 ((b.1, F.start₂ b.1.1), b.2))) →
    (∀ b s, F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s →
      L₃.rd0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) = L₂.rdZ b ∧
      (L₂.invZ b → L₃.inv0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2))) →
    (∀ b, Z.on (L₃.rdZ b) → L₃.invZ b → ∃ w, Z.relR (L₃.rdZ b) w) →
    RowFit (DK.at a) all all →
    L₁.Held εs → L₂.Held εs → L₃.Held εs →
    KeyCore Kc DK tFk tJk t3k silK F.run 1 εs

theorem keyCoreAtDesc : KeyCoreAtDesc := by
  intro a Kc DK TFk TJk T3k tFk tJk t3k silK all X₁ X₂ W F T J₁ J₂ Z L₁ L₂ L₃ εs hO e₁ e₂ e₃ hf
    w₁ w₂ w₃ hfirst hs₁ hs₂ hlast hfit d₁ d₂ d₃
  refine keyCoreAnti a Kc DK TFk TJk T3k tFk tJk t3k silK silK
    (runRow (atDesc F T).run₁ (atDesc F T).run₂ (atDesc F T).run₃) F.run 1 εs
    (fun _ _ _ _ h => h)
    (runGivesRowAt (ckP .two) (DK.at a) all Kc.conf.Rec X₁ X₂ W F T hO) ?_
  exact keyCoreOfDecides a Kc DK TFk TJk T3k tFk tJk t3k silK all _ _ _ _ _ F.Cl W (atDesc F T)
    J₁ J₂ Z L₁ L₂ L₃ εs e₁ e₂ e₃ hf w₁ w₂ w₃ hfirst (fun _ b => hs₁ b)
    (fun _ b s h => by
      obtain ⟨s₃, h1, h2⟩ := Option.map_eq_some_iff.1 h
      have h3 : F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s₃ := by
        cases hh : F.start₃ b.1.1.1 b.1.1.2 b.1.2 with
        | error e =>
          have h1' : (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s₃ := h1
          rw [hh] at h1'
          cases h1'
        | ok t =>
          have h1' : (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s₃ := h1
          rw [hh] at h1'
          exact congrArg Except.ok (Option.some.inj h1')
      rw [← h2]
      exact hs₂ b s₃ h3)
    (fun _ b _ => hlast b) hfit d₁ d₂ d₃

/-- **The key file's hypothesis on soundness at a description's own decision.** -/
def KeySoundAtDesc : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK DP : WholeD) (TFk TJk T3k TFp TJp T3p : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
    (runP : Kc.conf.X × Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
    (F : FileDescription Kc.conf.Rec)
    (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK F.run silP runP eL N early
      late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK F.run silP runP eL N early
                                      late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK F.run silP runP eL N early
                                       late) P),
    Tl.W.depthReqT = 0 → KeyCore Kc DK tFk tJk t3k silK F.run 1 U.εs →
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK F.run silP runP
                                                               eL N early late) P Tl U)

theorem keySoundAtDesc : KeySoundAtDesc := by
  intro a Kc DK DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP eL N early late
    F P Tl U hdep h
  rw [keySound_iff_core, hdep, pow_zero]
  exact h

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.keyCoreAtDesc
#print axioms VerifiableInference.Desc.Sound.keySoundAtDesc
