-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/PlainOfDataByMake.lean: THE PROOF FILE's TOP OF THE PLAIN ROAD WITH THE SHARED CHAIN's KEYS BY MAKE (`proofSound_at_descB_byMake`, Johnson/Desc/Sound/DescBByMake.lean) WITH ITS THREE PREMISES ON PIECES
AND DATA PAID: the sibling of `proofSoundPlainOfData` (Johnson/Flat/PlainOfData.lean). Against that one: OUT: the letter key · the key's laws inside e₂ · F₁ · oneKey. IN: e₂ : `EachLawsBN` at the key that is the
acting part at each border (`keyAt`) · opens ("the shared chain opens no tree of the first") · kS₂ with "the shared chain's start is a function of the record alone". Statement made of the top's own by program;
the proof: two calls (`paidAtDesc`; the top).
THE FENCE THAT EVERY LINE ON THE PROOF FILE's PLAIN ROAD CARRIES: at M := the table of joints' shadow ("there is a w") the premise `tie` is FALSE, so the
rule is empty there; the cure feeds the first chain's laws in the MAP form (Q₁ k a b := on₁ (k+1) b ∧ ∀ w, R₁ (k+1) b w → R₁ k a (E a b w)) and takes M a b := "there is a w with R₁ 0 a w whose token is b's heard
reply". Q₁ and M are letters of this rule: it bears either; which is laid in is the caller's.
Limits: those of the top: A RULE; no description of the protocol is laid in; no member of this list. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DescBByMake
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
open _root_.Compile.Joined (Chains Desc worst_le)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (F : FileDescription (Kc.conf.X × Kc.conf.Rec))
  {W : Type} (file : String)
  (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
  (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₃ F.lastChainFirstTreeNumber)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (dW wEnd : W)

set_option quotPrecheck false in
/-- The maker's cut of the description's own blocks. -/
local notation "TT" => piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd

variable (Pl : PPlaces (DP.at a) (allOf (DP.at a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **The proof file's top, the keys by make, the pieces and the data paid.** -/
theorem proofSoundPlainOfDataByMake (d : (F.XiPub × F.S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str)
    (w₀ : Kc.conf.Cells) (hD : F.data file = .ok (DP.at a)) (hS : F.sealLast = true)
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F TT).p₁ :: (atDesc F TT).l₁))
    (e₂ : EachLawsBN (keyAt Prod.snd (DP.at a).t₁ (atDesc F TT).p₂ (atDesc F TT).l₂) Pl.on₂ Pl.Q₂ N 0
      ((atDesc F TT).p₂ :: (atDesc F TT).l₂))
    (opens : ∀ r ∈ (DP.at a).ds₂, ∀ j ∈ r.opens, (DP.at a).t₁ ≤ j)
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F TT).p₃ :: (atDesc F TT).l₃))
    (G : Glues (atDesc F TT) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (kS₂ : Kc.conf.Rec → F.S₂) (one : ∀ x rec, F.start₂ (F.pub (x, rec)) = kS₂ rec)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at a) (allOf (DP.at a))).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F TT).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F TT).p₁ (atDesc F TT).l₁ (DP.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc F TT).p₂ (atDesc F TT).l₂ (DP.at a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDesc F TT).p₃ (atDesc F TT).l₃ (DP.at a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                                               F.run eL N early none) P Tl U) := by
  obtain ⟨hO, hf, fit⟩ := paidAtDesc _ W F file (DP.at a) hD hS (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃
    rest₁ rest₂ rest₃ dW wEnd
  exact proofSound_at_descB_byMake Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N early F
    (allOf (DP.at a)) TT Pl h₁ h₂ h₃ M L₁ L₂ P Tl U d w₀ hO hf fit e₁ e₂ opens e₃ G pubEarly kS₂ one
    tie b₁ b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofSoundPlainOfDataByMake
