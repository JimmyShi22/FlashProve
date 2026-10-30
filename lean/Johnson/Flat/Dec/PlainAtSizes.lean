-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/PlainAtSizes.lean: the two tops of Johnson/Flat/PlainOfData.lean at the names of
the frame with the entry file's three letters (Johnson/Flat/Dec/), at the full size, and at a gated
decision whose gate is open. Theorems.

Why. So that the two tops end at the very terms in which the conditional theorem's hypotheses are
asked at a description that fails closed: `CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl)` at runK := `gatedFileDecision
b FK.run`, and `CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl)` at runP := `gatedFileDecision b F.run`, with b = true.
The statements are made of PlainOfData.lean's by program: the configuration's letters := `lettersAt
A (relationsAndEncodingOfClaims A E)`; the silent rounds' fixed messages := the frame's; N := 2 ^ depthReq; εs := the
letters' own. Each proof: "subst", then one call.

Main names. `keySoundOfFullD_plain`, `proofSoundOfFullD_plain`.

Limits. Those of PlainOfData.lean: rules; no description is laid in; no member is shown. The full
size alone. Nothing on soundness of the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.PlainOfData
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

section Key
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {FK : FileDescription (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}
  {W : Type} (file : String)
  (c₁ : Block FK.S₁ FK.Cl) (k₁ : List (Block FK.S₁ FK.Cl)) (c₂ : Block FK.S₂ FK.Cl)
  (k₂ : List (Block FK.S₂ FK.Cl)) (c₃ : Block FK.S₃ FK.Cl) (k₃ : List (Block FK.S₃ FK.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (FK.XiPub ×
        FK.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) ((FK.XiPub ×
        FK.S₁) × FK.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ FK.lastChainFirstTreeNumber)
    ((FK.XiPub × FK.S₁ × FK.S₂) × FK.S₃) W ds)
  (dW wEnd : W)

variable (Pl : PPlaces (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (FK.XiPub × FK.S₁) ((FK.XiPub ×
    FK.S₁) × FK.S₂)
    ((FK.XiPub × FK.S₁ × FK.S₂) × FK.S₃))
  (h₁ : (rowIOR (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
      rest₃ dW wEnd)).p₁ (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
      rest₁ rest₂ rest₃ dW wEnd)).l₁).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
      rest₃ dW wEnd)).p₂ (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
      rest₁ rest₂ rest₃ dW wEnd)).l₂).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
      rest₃ dW wEnd)).p₃ (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
      rest₁ rest₂ rest₃ dW wEnd)).l₃).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₃)
  (M : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec × (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str →
    (FK.XiPub × FK.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
  (L₁ : (FK.XiPub × FK.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
  (L₂ : (FK.XiPub × FK.S₁ × FK.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
  (d : (FK.XiPub × FK.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)

include d in
/-- **The key file's hypothesis on soundness at the frame's names, at the gated decision, on the
plain road.** -/
theorem keySoundOfFullD_plain {b : Bool} (hb : b = true)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP (gatedFileDecision b FK.run) runP ds xs dec rK rP depthReq early
      salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP (gatedFileDecision b FK.run) runP ds xs dec rK rP depthReq early salt K P)
    (hD : FK.data file = .ok (DK.at frS.P.T.a)) (hS : FK.sealLast = true)
    (q₁ : FK.first.blocksInOrder = c₁ :: k₁) (q₂ : FK.shared.blocksInOrder = c₂ :: k₂) (q₃ : FK.second.blocksInOrder = c₃ ::
                          k₃)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁))
    (e₂ : EachLeads Pl.on₂ Pl.Q₂ 0 ((atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃))
    (G : Glues (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
        rest₃ dW wEnd)) Pl M L₁ L₂)
    (tie : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).sh) (s₁
          : FK.S₁) (s₂ : FK.S₂)
      (s₃ : FK.S₃) (z : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      FK.okStart rec = true →
      silK rec ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgF
          τ).2
        ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgJ τ).2
        ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msg3 τ).2 =
            true →
      FK.fin rec s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
          rest₃ dW wEnd)).in₁ rec, (y, fun _ => [])) → M (rec, y) ((FK.pub rec, s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 ∨ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none)
    (cS : ℝ≥0∞)
    (b₁ : Err.Below (errOwn (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁ (DK.at frS.P.T.a).ds₁ h₁) Tl.εs)
    (b₂ : Err.Below (errOwn (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂ (DK.at frS.P.T.a).ds₂ h₂) cS)
    (hc : ((2 ^ Tl.depthReqT : ℕ) : ℝ≥0∞) * cS ≤ Tl.εs)
    (b₃ : Err.Below (errOwn (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc FK (piecesAt (ckP .two) FK (DK.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃ (DK.at frS.P.T.a).ds₃ h₃) Tl.εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  subst hb
  exact keySoundPlainOfData (lettersAt A (relationsAndEncodingOfClaims A E)) DK DP (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty silK silP runP (linkProtocolAtFullSize ds xs dec salt) (2 ^
                   depthReq)
    early none FK file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Pl h₁ h₂ h₃ M L₁ L₂ d P
        Tl.letters
    Tl.names hD hS q₁ q₂ q₃ e₁ e₂ e₃ G tie cS b₁ b₂ hc b₃

end Key

section Proof
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {F : FileDescription ((lettersAt A (relationsAndEncodingOfClaims A E)).conf.X × (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec)}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : X → X}
  {salt K : ℕ}
  {W κ : Type} (file : String)
  (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
  (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁)
        W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁)
        × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (dW wEnd : W)

variable (Pl : PPlaces (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub ×
    F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
      rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁
      rest₂ rest₃ dW wEnd)).l₁).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
      rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁
      rest₂ rest₃ dW wEnd)).l₂).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
      rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁
      rest₂ rest₃ dW wEnd)).l₃).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₃)
  (M : ((lettersAt A (relationsAndEncodingOfClaims A E)).conf.X × (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec) × (oneExternalString (2 ^ (DP.at
                                                               frS.P.T.a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → κ)

/-- **The proof file's hypothesis on soundness at the frame's names, at the gated decision, on the
plain road.** -/
theorem proofSoundOfFullD_plain {b : Bool} (hb : b = true)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK (gatedFileDecision b F.run) ds xs dec rK rP depthReq early
      salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK (gatedFileDecision b F.run) ds xs dec rK rP depthReq early salt K P)
    (w₀ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Cells) (hD : F.data file = .ok (DP.at frS.P.T.a)) (hS :
                              F.sealLast = true)
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ (2 ^ depthReq) 0 ((atDesc F (piecesAt (ckP .two) F (DP.at
        frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP
        .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃))
    (G : Glues (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
        rest₃ dW wEnd)) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (F₁ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rec → (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (lettersAt A (relationsAndEncodingOfClaims A E)) DP (front₀ rP) (join₀ rP) ByteArray.empty F (allOf (DP.at
                                frS.P.T.a)) (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
                                dW wEnd) Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
          dW wEnd)).in₂ b.1, b.2) = F₁ rec y)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh) (s₁
          : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty).msgF τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msg3 τ).2 =
            true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
          rest₃ dW wEnd)).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none ∨ ∃ i, (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec
          = some i ∧ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁ (DP.at frS.P.T.a).ds₁ h₁) Tl.εs)
    (b₂ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂ (DP.at frS.P.T.a).ds₂ h₂) Tl.εs)
    (b₃ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃ (DP.at frS.P.T.a).ds₃ h₃) Tl.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl) := by
  subst hb
  exact proofSoundPlainOfData (lettersAt A (relationsAndEncodingOfClaims A E)) DK DP (front₀ rK) (join₀ rK)
      ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty silK runK silP (linkProtocolAtFullSize ds xs dec salt) (2 ^
                   depthReq)
    early F file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Pl h₁ h₂ h₃ M L₁ L₂ d key P Tl.letters
    Tl.names w₀ hD hS q₁ q₂ q₃ e₁ e₂ e₃ G pubEarly F₁ oneKey tie b₁ b₂ b₃

end Proof

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.keySoundOfFullD_plain
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfFullD_plain
