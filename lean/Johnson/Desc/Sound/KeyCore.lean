-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyCore.lean: WHAT THE KEY FILE'S NAMED HYPOTHESIS ON SOUNDNESS SAYS, WITHOUT
THE LETTERS THAT IT DOES NOT READ; and that it goes over to every decision that says yes less often.

The setting. `CompilerSoundnessConditionStatements.keySound` (Johnson/Top/InnerCompiledVerifier.lean) is stated at an input of the top
theorem. At the three protocols of `filesOf` (Johnson/EntryRec/AtFiles.lean) that input holds
provers, wires, the proof file and the entry file. The hypothesis reads of all that: the key file's
written rounds' data, its test on the silent rounds, its decision, the number of leaves of its
request tree, and εs.

What is said.
  `KeyCore Kc DK tF tJ t3 silK runK N εs`: there is a list of errors, each (a shared round's N
    times) a share of at most εs, at which the key file's verifier, with the decision runK, is
    round-by-round sound for "the stored table has a collision at the record's seed, or decodes with
    the record".
  `keySound_iff_core`: `CompilerSoundnessConditionStatements.keySound` at `filesOf` IS that, at N := 2 ^ depthReqT and the
    input's εs: by unfolding.
  `KeyCoreOfBlocks`, `keyCoreOfBlocks`: the rule `KeySoundOfBlocks`
    (Johnson/Desc/Sound/KeyRule.lean), its premises to the letter, ending in `KeyCore`: the same
    proof.
  `KeyCoreAnti`, `keyCoreAnti`: IF runK' SAYS YES ONLY WHERE runK DOES (and the like for the tests
    on the silent rounds), `KeyCore` AT runK GIVES `KeyCore` AT runK'.
`keyCore_no`: a decision that never says yes meets `KeyCore` at every N and εs: as it must: a
  verifier that never accepts is sound. (A decision that says yes to all: not tried here.)

Limits. Nothing on any decision of the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRule
import Johnson.Desc.Sound.DescDecidesProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.TypedOracleCompiler.Joined (Links row_sound)

/-- **What the key file's hypothesis on soundness says.** -/
def KeyCore {a : ℕ} (Kc : ConfLetters a) (DK : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ)
    (t3 : T3) (silK : Kc.conf.Rec → TF → TJ → T3 → Bool)
    (runK : Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool) (N : ℕ) (εs : ℝ≥0∞) : Prop :=
  ∃ ε, Err.Below (Err.timesShared N (chainsOf (ckP .two) (DK.at a) tF tJ t3).ann ε) εs ∧
    (reductionOfWholeFile (ckP .two) (DK.at a) tF tJ t3 silK runK).toInteractiveOracleProof.Sound
      (fun rec y => Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none) ε

/-- **The named hypothesis is that**, by unfolding. -/
theorem keySound_iff_core {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
    {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
    (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (runK : Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
    (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
    (runP : Kc.conf.X × Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
    (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
      late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                      late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                       late) P) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP
                                                               eL N early late) P Tl U) ↔
      KeyCore Kc DK tFk tJk t3k silK runK (2 ^ Tl.W.depthReqT) U.εs :=
  Iff.rfl

/-- **The rule at the key file, ending in `KeyCore`.** -/
def KeyCoreOfBlocks : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK : WholeD) (TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3)
    (silK : Kc.conf.Rec → TF → TJ → T3 → Bool)
    (all : List LeftT) (S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (okF : Kc.conf.Rec → TF → Bool)
    (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT (ckP .two) (DK.at a).ds₁)
    (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT (ckP .two) (DK.at a).ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT (ckP .two) (DK.at a).ds₃) (N : ℕ) (εs : ℝ≥0∞),
    T.Fits → EachGood Q.on₁ Q.R₁ 0 (T.p₁ :: T.l₁) → EachGood Q.on₂ Q.R₂ 0 (T.p₂ :: T.l₂) →
    EachGood Q.on₃ Q.R₃ 0 (T.p₃ :: T.l₃) → T.Glued Q →
    RowFit (DK.at a) all all →
    (∀ x u v c, silK x u v c = true → okF x u = true) →
    (∀ x u v c vw x₁, silK x u v c = true → T.run₁ x vw = some x₁ → okJ x₁ v = true) →
    (∀ x u v c vw vw' x₁ x₂, silK x u v c = true → T.run₁ x vw = some x₁ →
      T.run₂ x₁ vw' = some x₂ → ok3 x₂ c = true) →
    (∀ rec y, (Q.on₁ 0 (T.in₁ rec, (y, fun _ => [])) →
        ∃ w, Q.R₁ 0 (T.in₁ rec, (y, fun _ => [])) w) →
      Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none) →
    Err.Below (Err.timesShared N (chainsOf (ckP .two) (DK.at a) tF tJ t3).ann
      ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).err) εs →
    KeyCore Kc DK tF tJ t3 silK (runRow T.run₁ T.run₂ T.run₃) N εs

theorem keyCoreOfBlocks : KeyCoreOfBlocks := by
  intro a Kc DK TF TJ T3 tF tJ t3 silK all S₁ S₂ S₃ X₁ X₂ Cl W T Q okF okJ ok3 h₁ h₂ h₃ N εs hf g₁
    g₂ g₃ hgl hfit hF hJ h3 lang below
  have hk := fileKnows (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ
    t3 T Q okF okJ ok3 h₁ h₂ h₃ hf g₁ g₂ g₃ hgl
  have hd := fileDecides (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 tF
    tJ t3 T okF okJ ok3 silK (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃) hfit hF hJ h3
  have hs := row_sound (wholeDesc (ckP .two) (DK.at a) tF tJ t3 silK
    (runRow T.run₁ T.run₂ T.run₃)) hk (fun x y τ hacc => by
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hacc
      cases u
      exact hd x y τ hu)
  exact ⟨_, below, fun rec y hL => hs rec y fun h => hL (lang rec y h)⟩

/-- **It goes over to every decision that says yes less often.** -/
def KeyCoreAnti : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK : WholeD) (TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3)
    (silK silK' : Kc.conf.Rec → TF → TJ → T3 → Bool)
    (runK runK' : Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool) (N : ℕ) (εs : ℝ≥0∞),
    (∀ x u v c, silK' x u v c = true → silK x u v c = true) →
    (∀ x v₁ v₂ v₃, runK' x v₁ v₂ v₃ = true → runK x v₁ v₂ v₃ = true) →
    KeyCore Kc DK tF tJ t3 silK runK N εs → KeyCore Kc DK tF tJ t3 silK' runK' N εs

theorem keyCoreAnti : KeyCoreAnti := by
  intro a Kc DK TF TJ T3 tF tJ t3 silK silK' runK runK' N εs hsil hrun ⟨ε, hb, hs⟩
  refine ⟨ε, hb, fun x y hL => Doomed.mono _ _ (fun τ hτ => ?_) (hs x y hL)⟩
  show ((reductionOfWholeFile (ckP .two) (DK.at a) tF tJ t3 silK' runK').out x y τ).isSome = false
  have hτ' : ((reductionOfWholeFile (ckP .two) (DK.at a) tF tJ t3 silK runK).out x y τ).isSome = false := hτ
  cases ho : (reductionOfWholeFile (ckP .two) (DK.at a) tF tJ t3 silK' runK').out x y τ with
  | none => rfl
  | some u =>
    cases u
    rw [wholeMono (ckP .two) (DK.at a) Kc.conf.Rec TF TJ T3 tF tJ t3 silK' silK runK' runK x x
      (hsil x) (hrun x) y τ ho] at hτ'
    cases hτ'

/-- No error in any round. -/
def errZero : (s : Shape) → Err s
  | [] => ()
  | _ :: s => (0, errZero s)

theorem errZero_below (N : ℕ) (c : ℝ≥0∞) : ∀ (s : Shape) (A : Iop.RoundSplits s),
    Err.Below (Err.timesShared N A (errZero s)) c
  | [], _ => trivial
  | _ :: s, (a, A) => by
    refine ⟨?_, errZero_below N c s A⟩
    show ((match a.kind with | .lo => 0 | .sh => N * 0 : ℕ) : ℝ≥0∞) ≤ _
    cases a.kind <;> simp

/-- A decision that never says yes meets `KeyCore`. -/
theorem keyCore_no {a : ℕ} (Kc : ConfLetters a) (DK : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ)
    (t3 : T3) (silK : Kc.conf.Rec → TF → TJ → T3 → Bool) (N : ℕ) (εs : ℝ≥0∞) :
    KeyCore Kc DK tF tJ t3 silK (fun _ _ _ _ => false) N εs :=
  ⟨errZero _, errZero_below N εs _ _, fun x y _ => Doomed.of_forall _ _ fun τ => by
    show ((reductionOfWholeFile (ckP .two) (DK.at a) tF tJ t3 silK fun _ _ _ _ => false).out x y τ).isSome =
      false
    cases ho : (reductionOfWholeFile (ckP .two) (DK.at a) tF tJ t3 silK fun _ _ _ _ => false).out x y τ with
    | none => rfl
    | some u =>
      exfalso
      have h' : (if _ && false = true then some () else none) = some u := ho
      simp at h'⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.keyCore_no
#print axioms VerifiableInference.Desc.Sound.keySound_iff_core
#print axioms VerifiableInference.Desc.Sound.keyCoreOfBlocks
#print axioms VerifiableInference.Desc.Sound.keyCoreAnti
