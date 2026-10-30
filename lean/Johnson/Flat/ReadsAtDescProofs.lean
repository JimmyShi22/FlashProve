-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadsAtDescProofs.lean: the proofs of `OutRuns` and `ReadsOfHolds`
(Johnson/Flat/ReadsAtDesc.lean), each under its statement's name with a small first letter.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ReadsAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row)

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (F : VerifiableInference.Desc.FileDescription (Kc.conf.X × Kc.conf.Rec))
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : Kc.conf.X × Kc.conf.Rec → PQ.View → Option X₁) (run₂ : X₁ → PQ.View → Option X₂)
  (run₃ : X₂ → PQ.View → Bool)
  (S : (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd)
  {Tok : Type} (drop : Kc.conf.X → Tok) (tokW : S.W₀ → Tok)
  (rd : List Fmt.RoundView → Option Tok) (H : F.Hears (fun b => drop b.1) rd)
  (heardX : X₁ → Option Tok)

theorem outRuns : OutRuns Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S := by
  intro b τ₁ b₁ hb
  obtain ⟨x₁, hx, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hx' : (if (true : Bool) = true then
      (if sTests (ckP .two) ((DP.at a).st₁ L₁) (imp₁ (DP.at a) L₁ b.2) τ₁.2.2 then
        run₁ b.1 (sView (ckP .two) ((DP.at a).st₁ L₁) (imp₁ (DP.at a) L₁ b.2) τ₁.2.2) else none)
      else none) = some x₁ := hx
  rw [if_pos rfl] at hx'
  split at hx'
  · exact hx'
  · cases hx'

theorem readsOfHolds :
    ReadsOfHolds Kc DP tFp tJp t3p F L₁ L₂ run₁ run₂ run₃ S drop tokW rd H heardX := by
  intro fh rh b τ₁ w₁ b₁ hb
  have r := rh _ _ _ (outRuns Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S b τ₁ b₁ hb)
  exact r.symm.trans (fh b τ₁ w₁ b₁ hb)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.outRuns
#print axioms VerifiableInference.OnPublicFiles.readsOfHolds
