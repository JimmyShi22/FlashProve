-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfLawsBelow.lean: `ProofSoundOfLaws` (Johnson/Flat/ProofOfLaws.lean) WITH ITS
THREE BOUNDS ASKED BLOCK BY BLOCK: every block of the three chains has its own errors, as shares of
its rounds' challenges, at most U.εs (`EachBelow`, Johnson/Desc/Sound/BelowOfBlocks.lean). One
statement, written as `def … : Prop`, and its proof: `sndBelow` and `proofSoundOfLaws`.

So every premise that speaks of a number speaks of ONE BLOCK's numbers. For a block of the shared
chain whose own errors are εK + N · εO the bound is had from cK + N · cO ≤ U.εs (`belowBoth`).

Limits. Those of ProofOfLaws.lean and BelowOfBlocks.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfLawsProofs
import Johnson.Desc.Sound.BelowOfBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc.Sound
  (ThreeAt PlacesAt atDesc atDescFin FinGives OfDesc ExtRowAt rowIOR EAll EachGood
  EachLostBoth actsOf EachBelow sndBelow)

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (F : VerifiableInference.Desc.FileDescription (Kc.conf.X × Kc.conf.Rec))
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (all : List LeftT) {X₁ X₂ W : Type} (T : ThreeAt (ckP .two) (DP.at a) all F X₁ X₂ W)
  (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
  (Q : PlacesAt (DP.at a) all F W)

variable {Tok : Type} (drop : Kc.conf.X → Tok) (put : Kc.conf.X → Tok → Kc.conf.X) (tok : W → Tok)
  (rd : List Fmt.RoundView → Option Tok) (H : F.Hears (fun b => drop b.1) rd) (toW : W → Kc.conf.Cells)
  (back : F.XiPub → Kc.conf.X × Kc.conf.Rec) (s₂ : Kc.conf.Rec → F.S₂)
  (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **The proof file's named hypothesis on soundness, at a description's decision, from one law and
one bound a block.** -/
def ProofSoundOfLawsBelow : Prop :=
  OfDesc F T → FinGives F g → (atDescFin F g T).Fits →
  EachGood Q.on₁ Q.R₁ 0 ((atDescFin F g T).p₁ :: (atDescFin F g T).l₁) →
  EachLostBoth N Q.on₂ Q.R₂ (actsOf Prod.snd (DP.at a).t₁ (atDescFin F g T).p₂ (atDescFin F g T).l₂)
    0
    ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂) →
  EachGood Q.on₃ Q.R₃ 0 ((atDescFin F g T).p₃ :: (atDescFin F g T).l₃) →
  (atDescFin F g T).Glued Q →
  ExtRowAt tok rd H.pre.length (atDescFin F g T).p₁ (atDescFin F g T).l₁ →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str), F.okStart x = true →
    Kc.conf.D y x.2 ≠ none → Q.on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => []))) →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str) (w : W),
    Q.R₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])) w →
    firstRel Kc DP put tok toW (back (F.pub x), y) w) →
  PubEarly Kc early F.pub → PubKeeps Kc early F.pub back → PutEarly Kc early put →
  TieGlue Kc early drop put →
  (∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec) →
  RowFit (DP.at a) all all →
  (∀ d ∈ (DP.at a).ds₂, ∀ j ∈ d.opens, (DP.at a).t₁ ≤ j) →
  EachBelow U.εs ((atDescFin F g T).p₁ :: (atDescFin F g T).l₁) →
  EachBelow U.εs ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂) →
  EachBelow U.εs ((atDescFin F g T).p₃ :: (atDescFin F g T).l₃) →
  CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                                             eL N early none) P Tl U)

theorem proofSoundOfLawsBelow :
    ProofSoundOfLawsBelow Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early all T g Q
      drop
      put tok rd H toW back s₂ P Tl U := by
  intro hO hg hf g₁ g₂ g₃ hgl hext hon hR hpe hk hput glue hkey fit hop c₁ c₂ c₃
  have h₁ := (VerifiableInference.Desc.Sound.shapeIsChain _ _ _ (ckP .two) _ (atDescFin F g T).p₁
    (atDescFin F g T).l₁).trans (congrArg (uLT (ckP .two)) hf.data₁)
  have h₂ := (VerifiableInference.Desc.Sound.shapeIsChain _ _ _ (ckP .two) _ (atDescFin F g T).p₂
    (atDescFin F g T).l₂).trans (congrArg (uLT (ckP .two)) hf.data₂)
  have h₃ := (VerifiableInference.Desc.Sound.shapeIsChain _ _ _ (ckP .two) _ (atDescFin F g T).p₃
    (atDescFin F g T).l₃).trans (congrArg (uLT (ckP .two)) hf.data₃)
  obtain ⟨b₁, b₂, b₃⟩ := sndBelow (ckP .two) (DP.at a) all _ _ _ _ _ _ _ W _ _ _ tFp tJp t3p
    (atDescFin F g T) Q (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁ h₂ h₃ U.εs c₁ c₂ c₃
  exact proofSoundOfLaws Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early all T g Q h₁
    h₂
    h₃ drop put tok rd H toW back s₂ P Tl U hO hg hf g₁ g₂ g₃ hgl hext hon hR hpe hk hput glue hkey
      fit
    hop b₁ b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofSoundOfLawsBelow
