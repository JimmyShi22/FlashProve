-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfBlocksProofs.lean: the proof of `ProofSoundOfBlocks`
(Johnson/Flat/ProofOfBlocks.lean), under its name with a small first letter. A joining.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfBlocks
import Johnson.Flat.ProofOfDescRunsProofs
import Johnson.Desc.Sound.DescThreeProofs
import Johnson.Desc.Sound.ExtHeardProofs

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
  (ThreeAt PlacesAt atDesc atDescFin FinGives OfDesc ExtRowAt rowIOR HearsRowAt below
  runsAtDesc runGivesRowAtFin hearsRowOf firstHoldsAt leavesBelow laysBelow)
open VerifiableInference.Desc (leavesLiftIn laysLiftIn)

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
  (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)
  {κ₁ κ₂ : Type}
  (k₁ : (F.XiPub × F.S₁) × (rowP Kc DP tFp tJp t3p all all (atDescFin F g T).run₁ (atDescFin F g
  T).run₂
    (atDescFin F g T).run₃).E₁.Str → κ₁)
  (k₂ : (F.XiPub × F.S₁ × F.S₂) × (rowP Kc DP tFp tJp t3p all all (atDescFin F g T).run₁
    (atDescFin F g T).run₂ (atDescFin F g T).run₃).E₂.Str → κ₂)

theorem proofSoundOfBlocks :
    ProofSoundOfBlocks Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early all T g Q h₁ h₂
      h₃
      drop put tok rd H toW P Tl U k₁ k₂ := by
  intro hO hg hf fit hp knows glue onOk tells hext b₁ b₂ b₃
  obtain ⟨e₀, -, -⟩ := runsAtDesc _ _ all _ X₁ X₂ W F T hO
  have e₁ : (atDescFin F g T).run₁ = VerifiableInference.Desc.Sound.descRun₁ F := e₀
  have gives : RunGives Kc F.run (atDescFin F g T).run₁ (atDescFin F g T).run₂
    (atDescFin F g T).run₃ :=
    fun x v₁ v₂ v₃ h => runGivesRowAtFin _ _ all _ X₁ X₂ W F g T hO hg x v₁ v₂ v₃ h
  have kept : EarlyKept Kc early (atDescFin F g T).run₁ := by
    rw [e₁]
    exact keptAt Kc F early hp
  have heard : RunHeard Kc F (atDescFin F g T).run₁ drop rd H fun x₁ => H.heard x₁.2 := by
    rw [e₁]
    exact heardAt Kc F drop rd H
  have hrow : HearsRowAt tok (fun s : F.XiPub × F.S₁ => H.heard s.2) H.pre.length
    (atDescFin F g T).p₁
      (atDescFin F g T).l₁ :=
    hearsRowOf F.S₁ (F.XiPub × F.S₁) F.Cl W Tok _ _ tok H.heard (fun s => H.heard s.2) rd
      (fun b => (below b).lift Prod.snd fun t s => (t.1, s))
      (fun b hb => leavesLiftIn _ _ _ _ H.heard Prod.snd _ (below b) (fun _ _ => rfl)
        (leavesBelow _ _ _ H.heard b hb))
      (fun b hb => laysLiftIn _ _ _ _ H.heard rd Prod.snd _ (below b) (fun _ _ => rfl)
        (laysBelow _ _ _ H.heard rd b hb))
      H.pre H.blk H.post _ _
      (hO.b₁.trans (by rw [H.cut, List.map_map]; rfl)) H.lays H.leaves hext
  have holds : FirstHolds Kc DP tFp tJp t3p all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
      (atDescFin F g T).run₃ (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃) tok fun x₁ => H.heard
        x₁.2 :=
    firstHoldsAt _ _ all _ _ _ _ _ _ _ W _ _ _ Tok tFp tJp t3p (atDescFin F g T) Q _ _ _ h₁ h₂ h₃
      tok
      (fun s => H.heard s.2) H.pre.length id hf hrow fun _ _ => rfl
  exact proofSoundAtDesc Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early all all
    (atDescFin F g T).run₁ (atDescFin F g T).run₂ (atDescFin F g T).run₃
    (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃) drop put tok rd H toW P Tl U k₁ k₂ fit gives kept
    (endsAt _ F) knows glue onOk tells
    (readsOfHolds Kc DP tFp tJp t3p F all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
      (atDescFin F g T).run₃
      (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃) drop tok rd H (fun x₁ => H.heard x₁.2) holds
      heard) b₁ b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofSoundOfBlocks
