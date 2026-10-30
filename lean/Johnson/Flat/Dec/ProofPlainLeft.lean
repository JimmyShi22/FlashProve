-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Dec/ProofPlainLeft.lean: at the full size: what is left of the proof file's hypothesis
on soundness on the plain road, at the proof file's own description: the data and seven fields.

Why. `ProofPlainOwedAtF` (Johnson/Flat/Dec/ProofPlainAtF.lean) lists fourteen fields and, beside
them, three equations of shapes. Four tools in other files and the frame's own record pay six of
the fields and the three equations. A description's run asks its own tests on the plan first of all
(`F.planOk`: a test with code, which a run evaluates: nothing is assumed of a description), and
refuses where they say no: so the hypothesis may take them as given (`proofSoundOfFullD_of_planOk`,
Johnson/Flat/Dec/PlanOkForFree.lean): "sealed" is one of them. Where the description's own road
makes the data, none of its three chains is empty (`flatSome`,
Johnson/Desc/Sound/TilesDataProofs.lean): the three heads. Then the shared chain opens no tree of
the first (`sharedOpens_of_data`, Johnson/Desc/Sound/SharedOpensOfData.lean): "opens"; and the rows
of pieces have the data's shapes (`shapesOfData`, Johnson/Flat/PlainOfData.lean). "bound" is a field
of the frame's letters (`hε`, Johnson/Flat/Dec/TwoSizesAt.lean).
  `ProofPlainSevenAtF`: leads₁ leads₂ leads₃ glues pubEarly one tie: these fields of
  `ProofPlainOwedAtF`, to the token, BUT glues: its first implication is asked at the instances that
  instP makes alone (there it was asked at all of F's): just what the rule spends. The six others
  are typed at F; the rule takes them at `F.pull instP` by unfolding: a payer proves them at F.
  `ProofPlainLeft`: GIVEN the description's tests on the plan: F's own road makes the frame's data;
  and, GIVEN the three chains' first blocks and the rest, there are extractors, places, claims and a
  witness at which the seven hold. (What F's road returns is tied to the plan's rounds through these
  tests alone: so the data too are asked behind them.)
  `proofSound_plain_of_left`: it gives `CompilerSoundnessConditionStatements.proofSound` at every record of the frame's letters,
  whatever bound on a round's error that record names.
THE FENCE OF THE PROOF FILE's PLAIN ROAD STANDS HERE TOO: at a claim M that only says "there is a
witness", `tie` is false and the list empty.
THE LETTER M STANDS OVER THE INSTANCE (x, rec), not over the description's own type of instances:
what is known of the file's statement may read the request and the record themselves (so
`meansSome`, Johnson/Goal/Meaning/TieAtSome.lean, can be laid in). Who has an M over the
description's instances hands `fun a => M (instP a.1, a.2)`.
Limits. A RULE: NOTHING OF THE EIGHT (the data and the seven) IS PAID HERE. Where the tests on the
plan say no, `ProofPlainLeft` holds and nothing is owed: such a description accepts no proof.
Members are known at toys alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.PlainByMakeAtSizes
import Johnson.Desc.Sound.BoundsAtCap
import Johnson.Flat.Dec.PlanOkForFree
import Johnson.Desc.Sound.SharedOpensOfData
import Johnson.Desc.Sound.TilesDataProofs
import Johnson.Flat.PlainOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

/-- **Seven fields of `ProofPlainOwedAtF`.** -/
structure ProofPlainSevenAtF {X XiP : Type} (F : FileDescription XiP) (instP : X × RecFull → XiP)
    (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DP : WholeD) (rP : RecFull)
    (depthReq : ℕ) (early : X → X) {W : Type}
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (e₁ : (i : ℕ) → (ds : List RDT) → (F.XiPub × F.S₁) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₂ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁) × F.S₂) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₃ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (dW wEnd : W)
    (Pl : PPlaces (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (M : (X × RecFull) × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
      (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (w₀ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Cells)
    (kS₂ : RecFull → F.S₂) : Prop where
  leads₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₁)
  leads₂ : EachLawsBN (keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂) Pl.on₂ Pl.Q₂
    (2 ^ depthReq) 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂)
  leads₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₃)
  glues : Glues (atDesc (F.pull instP) (piecesAt (ckP .two) (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)) Pl
    M L₁ L₂
  pubEarly : ∀ x rec, F.pub (instP (early x, rec)) = F.pub (instP (x, rec))
  one : ∀ x rec, F.start₂ (F.pub (instP (x, rec))) = kS₂ rec
  tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh)
      (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃) (z : (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str),
      F.okStart (instP (x, rec)) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgF τ).2 ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgJ τ).2 ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msg3 τ).2 = true →
      F.fin (instP (x, rec)) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).in₁ (instP (early x, rec)), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (instP (x, rec)), s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none ∨
        ∃ i, (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = some i ∧ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Rno i x w₀

/-- **What is left of the proof file's hypothesis on the plain road.** -/
def ProofPlainLeft {X XiP : Type} (F : FileDescription XiP) (instP : X × RecFull → XiP)
    (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DP : WholeD) (rP : RecFull)
    (depthReq : ℕ) (early : X → X) : Prop :=
  F.planOk = true →
    F.data "proof file" = .ok (DP.at frS.P.T.a) ∧
      (∀ (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)),
        F.first.blocksInOrder = c₁ :: k₁ → F.shared.blocksInOrder = c₂ :: k₂ → F.second.blocksInOrder = c₃ :: k₃ →
        ∃ (W : Type) (e₁ : (i : ℕ) → (ds : List RDT) → (F.XiPub × F.S₁) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₂ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁) × F.S₂) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₃ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (dW wEnd : W)
    (Pl : PPlaces (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (M : (X × RecFull) × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
      (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (_d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
    (w₀ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Cells)
    (kS₂ : RecFull → F.S₂),
          ProofPlainSevenAtF F instP A E DP rP depthReq early c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd Pl M L₁ L₂ w₀ kS₂)

set_option maxHeartbeats 4000000 in
theorem proofSound_plain_of_left {X XiP : Type} (F : FileDescription XiP) (instP : X × RecFull → XiP)
    (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DP : WholeD) (rP : RecFull)
    (depthReq : ℕ) (early : X → X)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {b : Bool} (hb : b = true)
    {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} (er : runP = gatedFileDecision b (F.pull instP).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : ProofPlainLeft F instP A E DP rP depthReq early) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize Tl) := by
  refine proofSoundOfFullD_of_planOk (F.pull instP) b er Tl fun hp => ?_
  have hp' : F.planOk = true := (FileDescription.pull_planOk instP F).symm.trans hp
  obtain ⟨hD, h⟩ := h hp'
  obtain ⟨n₁, n₂, n₃⟩ := flatSome _ F "proof file" _ hD
  obtain ⟨c₁, k₁, q₁⟩ := List.exists_cons_of_ne_nil n₁
  obtain ⟨c₂, k₂, q₂⟩ := List.exists_cons_of_ne_nil n₂
  obtain ⟨c₃, k₃, q₃⟩ := List.exists_cons_of_ne_nil n₃
  obtain ⟨W, e₁, e₂, e₃, dW, wEnd, Pl, M, L₁, L₂, d, w₀, kS₂, g⟩ :=
    h c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃
  obtain ⟨h₁, h₂, h₃⟩ := shapesOfData (ckP .two) F "proof file" _ hD (sealLast_of_planOk F hp')
    c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd
  exact proofSoundOfFullD_byMake_at (F := (F.pull instP)) "proof file" c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd Pl
    h₁ h₂ h₃ M L₁ L₂ hb er Tl d w₀ hD
    (sealLast_of_planOk (F.pull instP) hp) q₁ q₂ q₃ g.leads₁ g.leads₂
    (sharedOpens_of_data F "proof file" _ hD) g.leads₃ g.glues g.pubEarly kS₂ g.one g.tie
    (below_atCap₁ (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd _ Tl.hε
      (atCap_restCap _) h₁)
    (below_atCap₂ (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd _ Tl.hε
      (atCap_restCap _) h₂)
    (below_atCap₃ (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd _ Tl.hε
      (atCap_restCap _) h₃)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofSound_plain_of_left
