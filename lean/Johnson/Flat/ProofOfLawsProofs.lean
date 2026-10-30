-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfLawsProofs.lean: the proof of `ProofSoundOfLaws`
(Johnson/Flat/ProofOfLaws.lean), under its name with a small first letter. A joining: four calls.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfLaws
import Johnson.Flat.ProofOfBlocksProofs

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
  EachLostBoth actsOf foldSlotsFin)

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
  (h₁ : (rowIOR (atDescFin F g T).p₁ (atDescFin F g T).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDescFin F g T).p₂ (atDescFin F g T).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDescFin F g T).p₃ (atDescFin F g T).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)

variable {Tok : Type} (drop : Kc.conf.X → Tok) (put : Kc.conf.X → Tok → Kc.conf.X) (tok : W → Tok)
  (rd : List Fmt.RoundView → Option Tok) (H : F.Hears (fun b => drop b.1) rd) (toW : W → Kc.conf.Cells)
  (back : F.XiPub → Kc.conf.X × Kc.conf.Rec) (s₂ : Kc.conf.Rec → F.S₂)
  (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

theorem proofSoundOfLaws :
    ProofSoundOfLaws Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early all T g Q h₁ h₂ h₃
      drop put tok rd H toW back s₂ P Tl U := by
  intro hO hg hf g₁ g₂ g₃ hgl hext hon hR hpe hk hput glue hkey fit hop b₁ b₂ b₃
  have knows := foldSlotsFin (ckP .two) (DP.at a) all Kc.conf.X Kc.conf.Rec X₁ X₂ W TFp TJp T3p tFp
    tJp
    t3p F g T Q (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁ h₂ h₃ N s₂ hO hf g₁ g₂ g₃
      hgl
    hop hkey
  exact proofSoundOfBlocks Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early all T g Q h₁
    h₂ h₃ drop put tok rd H toW P Tl U (fun a => (F.start₂ a.1.1, a.2.1)) (fun _ => ()) hO hg hf fit
    hpe knows glue (onOkAtBlocks Kc DP tFp tJp t3p silP F early all T g Q h₁ h₂ h₃ hpe hon)
    (tellsAtBlocks Kc DP tFp tJp t3p F early all T g Q h₁ h₂ h₃ put tok toW back hk hput hR) hext b₁
    b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofSoundOfLaws
