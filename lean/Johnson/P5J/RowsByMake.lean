-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RowsByMake.lean: THE ONE LEMMA, SECOND STOREY: `proofSound_at_descB_byMake`
(Johnson/Desc/Sound/DescBByMake.lean) WITH THE PROOF FILE'S SEVEN FIELDS (`VerifierAndGoals.AtTheName.RowsOfProofFile`,
Johnson/Goal/Skeleton/ProofFile.lean) IN THE PLACE OF `CompilerSoundnessConditionStatements.proofSound`: the premises to the letter, the
proof that theorem's own, turned by program at its one call.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DescBByMake
import Johnson.Goal.Skeleton.ProofRowsAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc worst_le)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (F : FileDescription (Kc.conf.X × Kc.conf.Rec)) (all : List LeftT) {X₁ X₂ W : Type}
  (T : ThreeAt (ckP .two) (DP.at a) all F X₁ X₂ W)
  (Pl : PPlaces (DP.at a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at a) all).Str → Prop)

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

open VerifierAndGoals.AtTheName

/-- **`CompilerSoundnessConditionStatements.proofSound` at a description's own decision, THE KEYS BY MAKE**:
`proofSound_at_descB` with the key at border k := the acting part there; of a shared block's files
the block's law and the hand-over of the condition alone are asked. -/
theorem rows_at_descB_byMake (d : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str)
    (w₀ : Kc.conf.Cells) (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (fit : RowFit (DP.at a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLawsBN (keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂) Pl.on₂ Pl.Q₂ N 0
      ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (opens : ∀ r ∈ (DP.at a).ds₂, ∀ j ∈ r.opens, (DP.at a).t₁ ≤ j)
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (k₂ : Kc.conf.Rec → F.S₂) (one : ∀ x rec, F.start₂ (F.pub (x, rec)) = k₂ rec)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F T).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at a).ds₃ h₃) U.εs) :
    RowsOfProofFile (b := soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                  F.run eL N early none) P Tl U)
      (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run)
      { w₀ := w₀
        P := plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d
        κ₁ := _
        k₁ := fun b => keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂ 0
          ((atDesc F T).in₂ b.1, b.2)
        F₁ := fun rec y => (k₂ rec, y, fun _ _ => none) } U.εs := by
  obtain ⟨g1, g2, hb⟩ := liftedAtDesc (ckP .two) (DP.at a) all _ X₁ X₂ W F T hO
  refine rows_at_descB Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N early F all T Pl
    h₁ h₂ h₃ M L₁ L₂ d (keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂) P Tl U w₀ hO
    hf fit e₁ ?_ e₃ G pubEarly (fun rec y => (k₂ rec, y, fun _ _ => none)) ?_ tie b₁ b₂ b₃
  · exact eachLeadsBNOfLaws _ _ _ _ _ _ _ _ _ N _ 0 e₂
      (keysByMake _ F.S₂ F.Cl W (ckP .two) _ Prod.snd
        (fun (t : (F.XiPub × F.S₁) × F.S₂) (s : F.S₂) => (t.1, s)) (DP.at a).t₁ (atDesc F T).p₂
        (atDesc F T).l₂ ((atDesc F T).in₂ d.1, d.2) g1 g2 hf.tiled₂ hb
        (fun q hq r hr => opens r
          (hf.data₂ ▸ mem_rowData (atDesc F T).p₂ (atDesc F T).l₂ q hq r hr)))
  · exact oneKeyByMake (ckP .two) (DP.at a) all _ _ X₁ X₂ W _ _ _ tFp tJp t3p F T (fun _ _ => true)
      (fun _ _ => true) (fun _ _ => true) h₁ h₂ h₃ k₂ hO hf one

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rows_at_descB_byMake
