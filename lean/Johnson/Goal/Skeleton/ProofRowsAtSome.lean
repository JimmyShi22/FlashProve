-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Skeleton/ProofRowsAtSome.lean: the seven fields of `VerifierAndGoals.AtTheName.RowsOfProofFile`
at a description's own plain file, WITH M LAID: M := `meansSome`
(Johnson/Goal/Meaning/TieAtSome.lean), the premise `tie` paid from `TieOwesSome`.

Why. `rows_at_descB` (Johnson/Goal/Skeleton/ProofRowsAtDesc.lean) takes the premise `tie` at a
letter M. `tie_of_some` gives that premise at M := `meansSome`, from two owed fields. That the one
fits the other to the letter is here one call.
  `rows_at_some`: at the full size's configuration kcReq N₀ pp E, in scope: the premises of
  `rows_at_descB` without `tie`, at M := `meansSome N₀ pp E DP F all X rep`, and `TieOwesSome`, give
  the seven fields.
  `proofSound_at_some`: the same premises give `CompilerSoundnessConditionStatements.proofSound` at the frame: `rows_at_some`
  laid on `proofSound_of_rows_at_descB`: the three joins in one term.
Limits. A JOINING OF RULES: NOTHING IS PAID; NO MEMBER. `TieOwesSome`'s two fields, the gluing at
`meansSome` (its first implication's second half is where the meaning is spent) and all other
premises are owed. The full size alone. No soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Skeleton.ProofRowsAtDesc
import Johnson.Goal.Meaning.TieAtSome

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Road OnBytes.Road.L5

variable (N₀ : MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N₀ pp)) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : (kcReq N₀ pp E).conf.Rec → TFk → TJk → T3k → Bool)
  (runK : (kcReq N₀ pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding (kcReq N₀ pp E).conf.Rec frS.P.T.a) (N : ℕ)
  (F : FileDescription ((kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec)) (all : List LeftT)
  {X₁ X₂ W κ : Type} (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W)
  (Pl : PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape =
    uLT (ckP .two) (DP.at frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape =
    uLT (ckP .two) (DP.at frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape =
    uLT (ckP .two) (DP.at frS.P.T.a).ds₃)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → κ)
  (X : OnBytes.Model.Verify.Public) (rep : F.XiPub × F.S₁ → Option (Fin Inst.Model.ppref.V))

variable (P : (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N
    reqWithoutReply none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                    eL N reqWithoutReply none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                     eL N reqWithoutReply none) P)

/-- **The seven fields with M laid.** -/
theorem rows_at_some {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (O : TieOwesSome N₀ pp E DP F all T Pl rep) (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (fit : RowFit (DP.at frS.P.T.a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl (meansSome N₀ pp E DP F all X rep) L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (F₁ : (kcReq N₀ pp E).conf.Rec → (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (kcReq N₀ pp E) DP tFp tJp t3p F all T Pl h₁ h₂ h₃
        (meansSome N₀ pp E DP F all X rep) L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at frS.P.T.a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at frS.P.T.a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at frS.P.T.a).ds₃ h₃) U.εs) :
    VerifierAndGoals.AtTheName.RowsOfProofFile
      (wholeDesc (ckP .two) (DP.at frS.P.T.a) tFp tJp t3p silP F.run)
      (lettersAtDescB (kcReq N₀ pp E) DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N
        reqWithoutReply F all T Pl h₁ h₂ h₃ (meansSome N₀ pp E DP F all X rep) L₁ L₂ d key P Tl U
        () F₁) U.εs :=
  rows_at_descB (kcReq N₀ pp E) DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N reqWithoutReply F
    all T Pl h₁ h₂ h₃ (meansSome N₀ pp E DP F all X rep) L₁ L₂ d key P Tl U () hO hf fit e₁ e₂ e₃ G
    pubEarly F₁ oneKey (tie_of_some N₀ pp E DP tFp tJp t3p silP F all T Pl X rep hZ hR h O) b₁ b₂ b₃

/-- **The three joins in one term.** -/
theorem proofSound_at_some {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (O : TieOwesSome N₀ pp E DP F all T Pl rep) (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (fit : RowFit (DP.at frS.P.T.a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl (meansSome N₀ pp E DP F all X rep) L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (F₁ : (kcReq N₀ pp E).conf.Rec → (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (kcReq N₀ pp E) DP tFp tJp t3p F all T Pl h₁ h₂ h₃
        (meansSome N₀ pp E DP F all X rep) L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at frS.P.T.a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at frS.P.T.a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at frS.P.T.a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf (kcReq N₀ pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               runK silP F.run eL N reqWithoutReply none) P Tl U) :=
  proofSound_of_rows_at_descB (kcReq N₀ pp E) DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N
    reqWithoutReply F all T Pl h₁ h₂ h₃ (meansSome N₀ pp E DP F all X rep) L₁ L₂ d key P Tl U () F₁
    (rows_at_some N₀ pp E DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N F all T Pl h₁ h₂ h₃ L₁
      L₂ d key X rep P Tl U hZ hR h O hO hf fit e₁ e₂ e₃ G pubEarly F₁ oneKey b₁ b₂ b₃)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rows_at_some
#print axioms VerifiableInference.OnPublicFiles.proofSound_at_some
