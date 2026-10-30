-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadsAtDesc.lean: `FirstReads` (Johnson/Flat/TiesSheet.lean) at the token that a
description's reply's block is shown (`saidP₁`, Johnson/Flat/TiesAtDesc.lean), from a law that names
no transcript's part: the token in the first chain's extractor's yield is what the statement that
the first chain HANDS ON holds as heard. A SHEET OF STATEMENTS: propositions written as `def … :
Prop`. NOTHING IS PROVED IN THIS FILE (the proofs: Johnson/Flat/ReadsAtDescProofs.lean).

Why. `FirstReads` compares the extractor's yield with a reading of the transcript. The blocks'
extractors composed are walked more easily against the carried record
(Johnson/Desc/Sound/ExtHeard.lean: `FirstHoldsAt`); and the record against the transcript is the
fold's matter (Johnson/Desc/Sound/FoldHeard.lean: `ChainLays`). Here the two are joined.

The letters, beside those of TiesAtDesc.lean. heardX: what a statement that the first chain hands on
holds as heard.

Main names.
  `OutRuns`: where the row's first reduction puts out b₁, the first run gave b₁'s explicit part on
    the first stage's own view.
  `FirstHolds`: where it puts out b₁, what b₁ holds as heard is the token in the first extractor's
    yield, whatever the later chains' witness.
  `RunHeard`: what the first run hands on holds as heard the token that the view names.
  `ReadsOfHolds`: `FirstHolds` and `RunHeard` give `FirstReads` at `saidP₁`.

Every "there is", walked. None of the statements has one.

Limits. At letters: the runs, S and heardX are tied to F by `RunHeard` alone. A first run that never
hands on meets `RunHeard` for nothing, and `FirstHolds` and `FirstReads` hold for nothing there too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TiesAtDesc

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

/-- Where the row's first reduction puts out b₁, the first run gave b₁'s explicit part on the first
stage's own view of the transcript behind the silent round. -/
def OutRuns : Prop :=
  ∀ b τ₁ b₁, (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).K₁.out b τ₁ = some b₁ →
    run₁ b.1 (sView (ckP .two) ((DP.at a).st₁ L₁) (imp₁ (DP.at a) L₁ b.2) τ₁.2.2) = some b₁.1

/-- Where the row's first reduction puts out b₁, what b₁ holds as heard is the token in the first
chain's extractor's yield, whatever the later chains' witness. -/
def FirstHolds : Prop :=
  ∀ b τ₁ w₁ b₁, (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).K₁.out b τ₁ = some b₁ →
    heardX b₁.1 = some (tokW ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).e₁ b τ₁ w₁))

/-- What the first run hands on holds as heard the token that the view names. -/
def RunHeard : Prop := ∀ b v x₁, run₁ b v = some x₁ → heardX x₁ = H.said v

/-- **`FirstReads` at the token that the reply's block is shown.** Meant by: `OutRuns`; the first
stage's view has the written rounds as its rounds, by unfolding. -/
def ReadsOfHolds : Prop :=
  FirstHolds Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S tokW heardX →
  RunHeard Kc F run₁ drop rd H heardX →
  FirstReads Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S tokW (saidP₁ Kc DP tFp tJp t3p F drop rd H)

end VerifiableInference.OnPublicFiles
