-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TiesAtDescProofs.lean: the proof of the statement of Johnson/Flat/TiesAtDesc.lean,
under its name with a small first letter.

How. The file's verifier's yes holds the decision's yes on the slot's three views
(`wholeIOR_out_eq`, OnBytes/Maker/RowWhole.lean); `EndsOfRun`; `saidOfEnds`
(Johnson/Desc/Sound/FoldHeardProofs.lean); the slot's first view has the written rounds as its
rounds, by unfolding.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TiesAtDesc
import Johnson.Desc.Sound.FoldHeardProofs

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
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (F : VerifiableInference.Desc.FileDescription (Kc.conf.X × Kc.conf.Rec))
  {Tok : Type} (drop : Kc.conf.X → Tok) (rd : List Fmt.RoundView → Option Tok)
  (H : F.Hears (fun b => drop b.1) rd)

theorem tieFinsAtDesc : TieFinsAtDesc Kc DP tFp tJp t3p silP F drop rd H := by
  intro ends x rec y τ ho
  rw [wholeIOR_out_eq] at ho
  split at ho
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨e₁, e₂, e₃, hch, hfin⟩ := ends _ _ _ _ hc.2
    have h := VerifiableInference.Desc.saidOfEnds _ F Tok (fun b => drop b.1) rd H (x, rec) _ _ e₁
      e₂ e₃ hch hfin
    exact h
  · cases ho

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.tieFinsAtDesc
