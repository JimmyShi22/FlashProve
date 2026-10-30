-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/PlainOfData.lean: the two tops of the rule of composition in the plain form
(`proofSound_at_descB`, Johnson/Desc/Plain/BothAtDesc.lean; `keySound_at_desc`,
Johnson/Desc/Plain/KeyAtDesc.lean) with their three premises on pieces and data shown. Theorems.

Why. The two tops take `OfDesc`, `Fits` and `RowFit` as premises. Here these fall out of both lists.
In their place stand two tests with code on the description (`F.data file = .ok (D.at a)`;
`F.sealLast = true`) and the three flat lists' heads as equations (which `flatSome` gives). The
statements are made of the two tops' own by program. Each proof is two calls: of `paidAtDesc`
(Johnson/Desc/Sound/PaidAtDesc.lean) and of the top.

The value. T := `piecesAt (ckP .two) F (D.at a) …`: the maker's cut of F's own blocks, each "below
b", lifted; all := `allOf (D.at a)`.

Main names.
  `shapesOfData`: the three equations of shapes (h₁ h₂ h₃ in the tops' statements) hold at that
    value.
  `proofSoundPlainOfData`, `keySoundPlainOfData`.

Limits. Those of the two tops: rules. No description of the protocol is laid in, and no member of
either list of premises is shown. The errors, block by block (rest₁ rest₂ rest₃), stay letters.
Nothing on soundness of the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Plain.BothAtDesc
import Johnson.Desc.Plain.KeyAtDesc
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)

/-- **The three equations of shapes at the maker's cut.** -/
theorem shapesOfData (C : CK) {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (hS : F.sealLast = true)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    rest₁ rest₂ rest₃ (dW wEnd : W) :
    (rowIOR (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁
        (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).shape = uLT C
            D.ds₁ ∧
      (rowIOR (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂
        (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).shape = uLT C
            D.ds₂ ∧
      (rowIOR (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃
        (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃).shape = uLT C
            D.ds₃ := by
  obtain ⟨-, hf, -⟩ := paidAtDesc Xi W F file D hD hS C c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃
      dW
    wEnd
  exact ⟨(shapeIsChain _ _ _ C _ _ _).trans (congrArg (uLT C) hf.data₁),
    (shapeIsChain _ _ _ C _ _ _).trans (congrArg (uLT C) hf.data₂),
    (shapeIsChain _ _ _ C _ _ _).trans (congrArg (uLT C) hf.data₃)⟩

end VerifiableInference.Desc.Sound

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc worst_le)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section Proof
variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (F : FileDescription (Kc.conf.X × Kc.conf.Rec))
  {W κ : Type} (file : String)
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
  (h₁ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DP.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at a) (allOf (DP.at a))).Str → κ)

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **The proof file's top in the plain form, the pieces and the data paid.** -/
theorem proofSoundPlainOfData (w₀ : Kc.conf.Cells) (hD : F.data file = .ok (DP.at a)) (hS :
    F.sealLast = true)
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F TT).p₁ :: (atDesc F TT).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDesc F TT).p₂ :: (atDesc F TT).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F TT).p₃ :: (atDesc F TT).l₃))
    (G : Glues (atDesc F TT) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (F₁ : Kc.conf.Rec → (oneExternalString (2 ^ (DP.at a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p F (allOf (DP.at a)) TT Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ =
          some b →
      key 0 ((atDesc F TT).in₂ b.1, b.2) = F₁ rec y)
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
  obtain ⟨hO, hf, fit⟩ := paidAtDesc _ W F file (DP.at a) hD hS (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂
      q₃
    rest₁ rest₂ rest₃ dW wEnd
  exact proofSound_at_descB Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N early F
    (allOf (DP.at a)) TT Pl h₁ h₂ h₃ M L₁ L₂ d key P Tl U w₀ hO hf fit e₁ e₂ e₃ G pubEarly F₁ oneKey
    tie b₁ b₂ b₃

end Proof

section Key
variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (FK : FileDescription Kc.conf.Rec)
  {W : Type} (file : String)
  (c₁ : Block FK.S₁ FK.Cl) (k₁ : List (Block FK.S₁ FK.Cl)) (c₂ : Block FK.S₂ FK.Cl)
  (k₂ : List (Block FK.S₂ FK.Cl)) (c₃ : Block FK.S₃ FK.Cl) (k₃ : List (Block FK.S₃ FK.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DK.at a) (allOf (DK.at a)) (DK.at a).key₁ 0) (FK.XiPub × FK.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DK.at a) (allOf (DK.at a)) (DK.at a).key₂ 0) ((FK.XiPub × FK.S₁) × FK.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DK.at a) (allOf (DK.at a)) (DK.at a).key₃ FK.lastChainFirstTreeNumber)
    ((FK.XiPub × FK.S₁ × FK.S₂) × FK.S₃) W ds)
  (dW wEnd : W)

set_option quotPrecheck false in
/-- The maker's cut of the description's own blocks. -/
local notation "TT" => piecesAt (ckP .two) FK (DK.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd

variable (Pl : PPlaces (DK.at a) (allOf (DK.at a)) (FK.XiPub × FK.S₁) ((FK.XiPub × FK.S₁) × FK.S₂)
    ((FK.XiPub × FK.S₁ × FK.S₂) × FK.S₃))
  (h₁ : (rowIOR (atDesc FK (piecesAt (ckP .two) FK (DK.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₁ (atDesc FK (piecesAt (ckP .two) FK (DK.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁).shape = uLT (ckP .two) (DK.at a).ds₁)
  (h₂ : (rowIOR (atDesc FK (piecesAt (ckP .two) FK (DK.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₂ (atDesc FK (piecesAt (ckP .two) FK (DK.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₂).shape = uLT (ckP .two) (DK.at a).ds₂)
  (h₃ : (rowIOR (atDesc FK (piecesAt (ckP .two) FK (DK.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).p₃ (atDesc FK (piecesAt (ckP .two) FK (DK.at a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₃).shape = uLT (ckP .two) (DK.at a).ds₃)
  (M : Kc.conf.Rec × (oneExternalString (2 ^ (DK.at a).a) SgX).Str →
    (FK.XiPub × FK.S₁) × (EAll (DK.at a) (allOf (DK.at a))).Str → Prop)
  (L₁ : (FK.XiPub × FK.S₁) × (EAll (DK.at a) (allOf (DK.at a))).Str → Prop)
  (L₂ : (FK.XiPub × FK.S₁ × FK.S₂) × (EAll (DK.at a) (allOf (DK.at a))).Str → Prop)
  (d : (FK.XiPub × FK.S₁) × (EAll (DK.at a) (allOf (DK.at a))).Str)

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early
    late).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early
                                    late) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early
                                     late) P)

include d in
/-- **The key file's top in the plain form, the pieces and the data paid.** -/
theorem keySoundPlainOfData (hD : FK.data file = .ok (DK.at a)) (hS : FK.sealLast = true)
    (q₁ : FK.first.blocksInOrder = c₁ :: k₁) (q₂ : FK.shared.blocksInOrder = c₂ :: k₂) (q₃ : FK.second.blocksInOrder = c₃ ::
                          k₃)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc FK TT).p₁ :: (atDesc FK TT).l₁))
    (e₂ : EachLeads Pl.on₂ Pl.Q₂ 0 ((atDesc FK TT).p₂ :: (atDesc FK TT).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc FK TT).p₃ :: (atDesc FK TT).l₃))
    (G : Glues (atDesc FK TT) Pl M L₁ L₂)
    (tie : ∀ rec (y : (oneExternalString (2 ^ (DK.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DK.at a) tFk tJk t3k).sh) (s₁ : FK.S₁) (s₂ : FK.S₂)
      (s₃ : FK.S₃) (z : (EAll (DK.at a) (allOf (DK.at a))).Str),
      FK.okStart rec = true →
      silK rec ((chainsOf (ckP .two) (DK.at a) tFk tJk t3k).msgF τ).2
        ((chainsOf (ckP .two) (DK.at a) tFk tJk t3k).msgJ τ).2
        ((chainsOf (ckP .two) (DK.at a) tFk tJk t3k).msg3 τ).2 = true →
      FK.fin rec s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc FK TT).in₁ rec, (y, fun _ => [])) → M (rec, y) ((FK.pub rec, s₁), z)) →
      Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none)
    (cS : ℝ≥0∞)
    (b₁ : Err.Below (errOwn (atDesc FK TT).p₁ (atDesc FK TT).l₁ (DK.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc FK TT).p₂ (atDesc FK TT).l₂ (DK.at a).ds₂ h₂) cS)
    (hc : ((2 ^ Tl.W.depthReqT : ℕ) : ℝ≥0∞) * cS ≤ U.εs)
    (b₃ : Err.Below (errOwn (atDesc FK TT).p₃ (atDesc FK TT).l₃ (DK.at a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP
                                                               runP eL N early late) P Tl U) := by
  obtain ⟨hO, hf, fit⟩ := paidAtDesc _ W FK file (DK.at a) hD hS (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂
      q₃
    rest₁ rest₂ rest₃ dW wEnd
  exact keySound_at_desc Kc DK DP tFk tJk t3k tFp tJp t3p silK silP runP eL N early late FK
    (allOf (DK.at a)) TT Pl h₁ h₂ h₃ M L₁ L₂ d P Tl U hO hf fit e₁ e₂ e₃ G tie cS b₁ b₂ hc b₃

end Key

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Desc.Sound.shapesOfData
#print axioms VerifiableInference.OnPublicFiles.proofSoundPlainOfData
#print axioms VerifiableInference.OnPublicFiles.keySoundPlainOfData
