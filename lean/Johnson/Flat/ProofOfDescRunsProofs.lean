-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfDescRunsProofs.lean: the proofs of the five statements of
Johnson/Flat/ProofOfDescRuns.lean, each under its statement's name with a small first letter.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfDescRuns
import Johnson.Flat.ProofOfDescProofs
import Johnson.Flat.ReadsAtDescProofs
import Johnson.Desc.Sound.DescRunsProofs

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
open VerifiableInference.Desc.Sound (descRun₁ descRun₂ descRun₃ runEndIs runGivesRow)

/-- Where a description's first run hands x₁ on: its first chain's fold ended at x₁'s record. -/
theorem chainOfRun₁ {Xi : Type} (F : VerifiableInference.Desc.FileDescription Xi) (x : Xi) (v : Fmt.View)
    (x₁ : F.XiPub × F.S₁) (h : descRun₁ F x v = some x₁) :
    VerifiableInference.Desc.chainAt "the first chain" 0 F.first.blocksInOrder (F.start₁ (F.pub x))
      (VerifiableInference.Desc.withEmptySealRound v) = .ok x₁.2 := by
  unfold descRun₁ at h
  split at h
  · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    cases hc : VerifiableInference.Desc.chainAt "the first chain" 0 F.first.blocksInOrder
        (F.start₁ (F.pub x)) (VerifiableInference.Desc.withEmptySealRound v) with
    | error e => rw [hc] at hs; exact nomatch hs
    | ok s' =>
      rw [hc] at hs
      exact congrArg Except.ok (Option.some.inj hs)
  · cases h

theorem endsAt : EndsAt := by
  intro Xi F x v₁ v₂ v₃ hr
  cases he : F.runEnd x v₁ v₂ v₃ with
  | error e =>
    have hr' : (F.runEnd x v₁ v₂ v₃).isOk = true := hr
    rw [he] at hr'
    exact nomatch hr'
  | ok ends =>
    obtain ⟨e₁, e₂, e₃⟩ := ends
    obtain ⟨_, _, h₁, _, _, _, hf⟩ := (runEndIs Xi F x v₁ v₂ v₃ e₁ e₂ e₃).1 he
    exact ⟨e₁, e₂, e₃, chainOfRun₁ F x v₁ _ h₁, hf⟩

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (F : VerifiableInference.Desc.FileDescription (Kc.conf.X × Kc.conf.Rec))
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (L₁ L₂ : List LeftT)
  (S : (rowP Kc DP tFp tJp t3p L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F)).Snd)
  {Tok : Type} (drop : Kc.conf.X → Tok) (put : Kc.conf.X → Tok → Kc.conf.X) (tokW : S.W₀ → Tok)
  (rd : List Fmt.RoundView → Option Tok) (H : F.Hears (fun b => drop b.1) rd)
  (toW : S.W₀ → Kc.conf.Cells)

theorem givesAt : GivesAt Kc F := fun x v₁ v₂ v₃ h => runGivesRow _ F x v₁ v₂ v₃ h

theorem keptAt : KeptAt Kc F early := by
  intro hp x rec v
  unfold descRun₁
  rw [hp x rec]

theorem heardAt : HeardAt Kc F drop rd H := by
  intro b v x₁ h
  have hc := chainOfRun₁ F b v x₁ h
  rw [H.cut] at hc
  exact VerifiableInference.Desc.chainLays F.S₁ F.Cl (Option Tok) H.heard rd _ 0 H.pre H.blk H.post
    _ x₁.2 (VerifiableInference.Desc.withEmptySealRound v) H.lays H.leaves hc

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (T : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)
  {κ₁ κ₂ : Type}
  (k₁ : (F.XiPub × F.S₁) ×
    (rowP Kc DP tFp tJp t3p L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F)).E₁.Str → κ₁)
  (k₂ : (F.XiPub × F.S₁ × F.S₂) ×
    (rowP Kc DP tFp tJp t3p L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F)).E₂.Str → κ₂)

theorem proofSoundAtRuns :
    ProofSoundAtRuns Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early L₁ L₂ S drop put
      tokW rd H toW P T U k₁ k₂ := by
  intro fit hp knows glue onOk tells holds b₁ b₂ b₃
  exact proofSoundAtDesc Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early L₁ L₂
    (descRun₁ F) (descRun₂ F) (descRun₃ F) S drop put tokW rd H toW P T U k₁ k₂ fit
    (givesAt Kc F) (keptAt Kc F early hp) (endsAt _ F) knows glue onOk tells
    (readsOfHolds Kc DP tFp tJp t3p F L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F) S drop tokW rd H
      (fun x₁ => H.heard x₁.2) holds (heardAt Kc F drop rd H)) b₁ b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.endsAt
#print axioms VerifiableInference.OnPublicFiles.givesAt
#print axioms VerifiableInference.OnPublicFiles.keptAt
#print axioms VerifiableInference.OnPublicFiles.heardAt
#print axioms VerifiableInference.OnPublicFiles.proofSoundAtRuns
