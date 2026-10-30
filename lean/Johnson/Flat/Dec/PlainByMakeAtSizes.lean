-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Dec/PlainByMakeAtSizes.lean: `proofSoundPlainOfDataByMake` (Johnson/Flat/PlainOfDataByMake.lean) AT THE NAMES OF THE FRAME WITH THE ENTRY FILE's THREE LETTERS, AT THE FULL SIZE: at a gated decision whose
gate is open (`proofSoundOfFullD_byMake`), and with the decision a letter and an equation (`proofSoundOfFullD_byMake_at`: runP = `gatedFileDecision b F.run`). The sibling of `proofSoundOfFullD_plain`
(Dec/PlainAtSizes.lean). Statements by program; each proof: "subst", one call.
THE FENCE THAT EVERY LINE ON THE PROOF FILE's PLAIN ROAD CARRIES: at M := the table of joints' shadow ("there is a w") the premise `tie` is FALSE, so the
rule is empty there; the cure feeds the first chain's laws in the MAP form (Q₁ k a b := on₁ (k+1) b ∧ ∀ w, R₁ (k+1) b w → R₁ k a (E a b w)) and takes M a b := "there is a w with R₁ 0 a w whose token is b's heard
reply". Q₁ and M are letters of this rule: it bears either; which is laid in is the caller's.
Limits: those of the file beneath. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.PlainOfDataByMake
import Johnson.Flat.Dec.ClosedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {F : FileDescription ((lettersAt A (relationsAndEncodingOfClaims A E)).conf.X × (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec)}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : X → X}
  {salt K : ℕ}
  {W : Type} (file : String)
  (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
  (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (dW wEnd : W)

variable (Pl : PPlaces (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₃)
  (M : ((lettersAt A (relationsAndEncodingOfClaims A E)).conf.X × (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec) × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)

/-- **At the gated decision, where the gate is open.** -/
theorem proofSoundOfFullD_byMake {b : Bool} (hb : b = true)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK (gatedFileDecision b F.run) ds xs dec rK rP depthReq early
      salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK (gatedFileDecision b F.run) ds xs dec rK rP depthReq early salt K P)
    (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
    (w₀ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Cells) (hD : F.data file = .ok (DP.at frS.P.T.a)) (hS : F.sealLast = true)
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁))
    (e₂ : EachLawsBN (keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) Pl.on₂ Pl.Q₂ (2 ^ depthReq) 0
      ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂))
    (opens : ∀ r ∈ (DP.at frS.P.T.a).ds₂, ∀ j ∈ r.opens, (DP.at frS.P.T.a).t₁ ≤ j)
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃))
    (G : Glues (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (kS₂ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec → F.S₂) (one : ∀ x rec, F.start₂ (F.pub (x, rec)) = kS₂ rec)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgF τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none ∨ ∃ i, (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = some i ∧ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁ (DP.at frS.P.T.a).ds₁ h₁) Tl.εs)
    (b₂ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂ (DP.at frS.P.T.a).ds₂ h₂) Tl.εs)
    (b₃ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃ (DP.at frS.P.T.a).ds₃ h₃) Tl.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl) := by
  subst hb
  exact proofSoundPlainOfDataByMake (lettersAt A (relationsAndEncodingOfClaims A E)) DK DP (front₀ rK) (join₀ rK)
    ByteArray.empty (front₀ rP) (join₀ rP) ByteArray.empty silK runK silP (linkProtocolAtFullSize ds xs dec salt)
    (2 ^ depthReq) early F file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Pl h₁ h₂ h₃ M L₁ L₂ P Tl.letters Tl.names
    d w₀ hD hS q₁ q₂ q₃ e₁ e₂ opens e₃ G pubEarly kS₂ one tie b₁ b₂ b₃

/-- **With the decision a letter and an equation.** -/
theorem proofSoundOfFullD_byMake_at {b : Bool} (hb : b = true)
    {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} (er : runP = gatedFileDecision b F.run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
    (w₀ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Cells) (hD : F.data file = .ok (DP.at frS.P.T.a)) (hS : F.sealLast = true)
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁))
    (e₂ : EachLawsBN (keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) Pl.on₂ Pl.Q₂ (2 ^ depthReq) 0
      ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂))
    (opens : ∀ r ∈ (DP.at frS.P.T.a).ds₂, ∀ j ∈ r.opens, (DP.at frS.P.T.a).t₁ ≤ j)
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃))
    (G : Glues (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (kS₂ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec → F.S₂) (one : ∀ x rec, F.start₂ (F.pub (x, rec)) = kS₂ rec)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgF τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none ∨ ∃ i, (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = some i ∧ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁ (DP.at frS.P.T.a).ds₁ h₁) Tl.εs)
    (b₂ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂ (DP.at frS.P.T.a).ds₂ h₂) Tl.εs)
    (b₃ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃ (DP.at frS.P.T.a).ds₃ h₃) Tl.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl) := by
  subst er
  exact proofSoundOfFullD_byMake file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Pl h₁ h₂ h₃ M L₁ L₂ hb Tl
    d w₀ hD hS q₁ q₂ q₃ e₁ e₂ opens e₃ G pubEarly kS₂ one tie b₁ b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofSoundOfFullD_byMake
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfFullD_byMake_at
