-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfDescProofs.lean: the proofs of the two statements of
Johnson/Flat/ProofOfDesc.lean, each under its statement's name with a small first letter. Joinings:
one call each of `rowDecides`, `readsOfFirst`, `tieFinsAtDesc`, `tiesOfFive`, `proofSoundOfRow`.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfDesc
import Johnson.Flat.TiesAtDescProofs
import Johnson.Flat.TiesSheetProofs
import Johnson.Flat.ProofOfRowProofs

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

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (F : VerifiableInference.Desc.FileDescription (Kc.conf.X × Kc.conf.Rec))
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : Kc.conf.X × Kc.conf.Rec → PQ.View → Option X₁) (run₂ : X₁ → PQ.View → Option X₂)
  (run₃ : X₂ → PQ.View → Bool)
  (S : (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd)
  {Tok : Type} (drop : Kc.conf.X → Tok) (put : Kc.conf.X → Tok → Kc.conf.X) (tokW : S.W₀ → Tok)
  (rd : List Fmt.RoundView → Option Tok) (H : F.Hears (fun b => drop b.1) rd)
  (toW : S.W₀ → Kc.conf.Cells)

theorem rowTiesAtDesc :
    RowTiesAtDesc Kc DP tFp tJp t3p silP F early L₁ L₂ run₁ run₂ run₃ S drop put tokW rd H toW := by
  intro fit gives kept ends glue onOk tells first
  exact tiesOfFive Kc DP tFp tJp t3p silP F.run early L₁ L₂ run₁ run₂ run₃ S drop put tokW
    (saidP Kc DP tFp tJp t3p F drop rd H) toW glue onOk tells
    (readsOfFirst Kc DP tFp tJp t3p silP F.run early L₁ L₂ run₁ run₂ run₃ S tokW
      (saidP₁ Kc DP tFp tJp t3p F drop rd H)
      (rowDecides Kc DP tFp tJp t3p silP F.run early L₁ L₂ run₁ run₂ run₃ S fit gives kept) first)
    (tieFinsAtDesc Kc DP tFp tJp t3p silP F drop rd H ends)

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (T : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)
  {κ₁ κ₂ : Type} (k₁ : X₁ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₁.Str → κ₁)
  (k₂ : X₂ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₂.Str → κ₂)

theorem proofSoundAtDesc :
    ProofSoundAtDesc Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL N early L₁ L₂ run₁ run₂
      run₃ S drop put tokW rd H toW P T U k₁ k₂ := by
  intro fit gives kept ends knows glue onOk tells first b₁ b₂ b₃
  exact proofSoundOfRow Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early L₁ L₂ run₁
    run₂ run₃ S P T U k₁ k₂ toW fit gives kept knows
    (rowTiesAtDesc Kc DP tFp tJp t3p silP F early L₁ L₂ run₁ run₂ run₃ S drop put tokW rd H toW fit
      gives kept ends glue onOk tells first) b₁ b₂ b₃

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rowTiesAtDesc
#print axioms VerifiableInference.OnPublicFiles.proofSoundAtDesc
