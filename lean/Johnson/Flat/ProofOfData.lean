-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfData.lean: THE PROOF FILE's NAMED HYPOTHESIS ON SOUNDNESS AT A DESCRIPTION's OWN DECISION (Johnson/Flat/ProofOfLawsBelow.lean), WITH ITS
THREE PREMISES ON PIECES AND DATA PAID: `OfDesc`, `Fits`, `RowFit` fall out of the list; in their place stand two tests with code on the description
(`F.data file = .ok (DP.at a)`; `F.sealLast = true`) and the three flat lists' heads as equations.
The proof file's sibling of Johnson/Flat/KeyOfData.lean [not in this library]. One
statement, written as `def … : Prop`, and its proof: TWO CALLS: of `paidAtDesc` (Johnson/Desc/Sound/PaidAtDesc.lean: a joining over the tiling in the rule of
composition's files, Johnson/Desc/Sound/Tiles*.lean) and of `proofSoundOfLawsBelow`.
THE VALUE: T := `piecesAt (ckP .two) F (DP.at a) …`; all := `allOf (DP.at a)`. The extractors and the errors, block by block, stay letters.
Limits: those of ProofOfLawsBelow.lean: A RULE; NO DESCRIPTION OF THE PROTOCOL IS LAID IN; no member of this list yet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfLawsBelow
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound (PlacesAt atDescFin FinGives ExtRowAt EachGood EachLostBoth actsOf
  EachBelow allOf piecesAt paidAtDesc Rest frameAt)

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (F : FileDescription (Kc.conf.X × Kc.conf.Rec))
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  {W : Type} (file : String)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
  (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₃ F.lastChainFirstTreeNumber)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (d wEnd : W) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
  (Q : PlacesAt (DP.at a) (allOf (DP.at a)) F W)

variable {Tok : Type} (drop : Kc.conf.X → Tok) (put : Kc.conf.X → Tok → Kc.conf.X) (tok : W → Tok)
  (rd : List Fmt.RoundView → Option Tok) (H : F.Hears (fun b => drop b.1) rd) (toW : W → Kc.conf.Cells)
  (back : F.XiPub → Kc.conf.X × Kc.conf.Rec) (s₂ : Kc.conf.Rec → F.S₂)
  (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

set_option quotPrecheck false in
/-- The maker's cut of the description's own blocks. -/
local notation "TP" => piecesAt (ckP .two) F (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd

/-- **The proof file's named hypothesis on soundness, at a description's decision, the pieces and the data
paid.** -/
def ProofSoundOfData : Prop :=
  F.data file = .ok (DP.at a) → F.sealLast = true →
  F.first.blocksInOrder = b₁ :: l₁ → F.shared.blocksInOrder = b₂ :: l₂ → F.second.blocksInOrder = b₃ :: l₃ →
  FinGives F g →
  EachGood Q.on₁ Q.R₁ 0 ((atDescFin F g TP).p₁ :: (atDescFin F g TP).l₁) →
  EachLostBoth N Q.on₂ Q.R₂ (actsOf Prod.snd (DP.at a).t₁ (atDescFin F g TP).p₂ (atDescFin F g TP).l₂)
    0
    ((atDescFin F g TP).p₂ :: (atDescFin F g TP).l₂) →
  EachGood Q.on₃ Q.R₃ 0 ((atDescFin F g TP).p₃ :: (atDescFin F g TP).l₃) →
  (atDescFin F g TP).Glued Q →
  ExtRowAt tok rd H.pre.length (atDescFin F g TP).p₁ (atDescFin F g TP).l₁ →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str), F.okStart x = true →
    Kc.conf.D y x.2 ≠ none → Q.on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => []))) →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str) (w : W),
    Q.R₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])) w →
    firstRel Kc DP put tok toW (back (F.pub x), y) w) →
  PubEarly Kc early F.pub → PubKeeps Kc early F.pub back → PutEarly Kc early put →
  TieGlue Kc early drop put →
  (∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec) →
  (∀ d ∈ (DP.at a).ds₂, ∀ j ∈ d.opens, (DP.at a).t₁ ≤ j) →
  EachBelow U.εs ((atDescFin F g TP).p₁ :: (atDescFin F g TP).l₁) →
  EachBelow U.εs ((atDescFin F g TP).p₂ :: (atDescFin F g TP).l₂) →
  EachBelow U.εs ((atDescFin F g TP).p₃ :: (atDescFin F g TP).l₃) →
  CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                                             eL N early none) P Tl U)

theorem proofSoundOfData :
    ProofSoundOfData Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early file b₁ l₁ b₂ l₂ b₃
      l₃ rest₁ rest₂ rest₃ d wEnd g Q drop put tok rd H toW back s₂ P Tl U := by
  intro hD hS e₁ e₂ e₃ hg
  obtain ⟨hO, hF, hR⟩ := paidAtDesc _ W F file (DP.at a) hD hS (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃
    rest₁ rest₂ rest₃ d wEnd
  intro g₁ g₂ g₃ hgl hext hon hRel hpe hk hput glue hkey hop c₁ c₂ c₃
  exact proofSoundOfLawsBelow Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early
    (allOf (DP.at a)) TP g Q drop put tok rd H toW back s₂ P Tl U hO hg
    ⟨hF.data₁, hF.data₂, hF.data₃, hF.base₁, hF.base₂, hF.base₃, hF.tiled₁, hF.tiled₂, hF.tiled₃⟩
    g₁ g₂ g₃ hgl hext hon hRel hpe hk hput glue hkey hR hop c₁ c₂ c₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofSoundOfData
