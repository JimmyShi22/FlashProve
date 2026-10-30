-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfDescRuns.lean: the proof file's named hypothesis on soundness
(`CompilerSoundnessConditionStatements.proofSound`) where the proof file's decision is a description's (`FileDescription.run`) AND THE
THREE RUNS ARE THAT DESCRIPTION's OWN (`descRun₁`, `descRun₂`, `descRun₃`:
Johnson/Desc/Sound/DescRuns.lean). A SHEET OF STATEMENTS: propositions written as `def … : Prop`.
NOTHING IS PROVED IN THIS FILE (the proofs: Johnson/Flat/ProofOfDescRunsProofs.lean).

Why. Johnson/Flat/ProofOfDesc.lean leaves the three runs letters beside the description, tied to it
by three premises on the description's text (gives, kept, ends). DescRuns.lean writes the runs out
and says what lies between them and the decision (`RunEndIs`, `RunGivesRow`). Here the three
premises are had from these two, and a fourth (`RunHeard`, Johnson/Flat/ReadsAtDesc.lean) from the
fold's law: so NO PREMISE ON THE DESCRIPTION's TEXT IS LEFT but `F.Hears` and "`early` keeps the
public part".

Main names.
  `EndsAt`: `EndsOfRun F`, at every description (from `RunEndIs`).
  `GivesAt`: `RunGives` at F's decision and F's runs (`RunGivesRow`).
  `KeptAt`: `PubEarly` at F's own pub gives `EarlyKept` at F's first run.
  `HeardAt`: `RunHeard` at F's first run: what it hands on holds as heard the token that the view
    names.
  `ProofSoundAtRuns`: THE HYPOTHESIS AT runP := F.run. WHAT IS LEFT, ALL NAMED: fit (a test on data)
    · pubEarly · H : `F.Hears` · knows · glue · onOk · tells · holds (`FirstHolds`: the token in the
    first chain's extractor's yield is what the handed-on record holds as heard) · three bounds.

Every "there is", walked. None is new here. `RunEndIs` has one ("there is a first record s₃"): the
value of `start₃`: determined.

Limits. Those of ProofOfDesc.lean. NO DESCRIPTION OF THE PROTOCOL IS LAID IN. A description that
never says yes meets all that is asked of F's text for nothing.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfDesc
import Johnson.Flat.ReadsAtDesc
import Johnson.Flat.TiesFilling
import Johnson.Desc.Sound.DescRuns

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
open VerifiableInference.Desc.Sound (descRun₁ descRun₂ descRun₃)

/-- At every description: where the decision says yes, the first chain's fold has ended and the last
test has said yes at that end. -/
def EndsAt : Prop :=
  ∀ (Xi : Type) (F : VerifiableInference.Desc.FileDescription Xi), EndsOfRun F

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

/-- The decision's yes gives the three runs'. -/
def GivesAt : Prop :=
  RunGives Kc F.run (descRun₁ F) (descRun₂ F) (descRun₃ F)

/-- Where `early` keeps the description's public part, the first run reads an instance through what
`early` keeps. -/
def KeptAt : Prop :=
  PubEarly Kc early F.pub → EarlyKept Kc early (descRun₁ F)

/-- What the first run hands on holds as heard the token that the view names. -/
def HeardAt : Prop :=
  RunHeard Kc F (descRun₁ F) drop rd H fun x₁ => H.heard x₁.2

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

/-- **The proof file's named hypothesis on soundness, at a description's decision and its own three
runs.** Meant by: `EndsAt`; `GivesAt`; `KeptAt`; `HeardAt` with `ReadsOfHolds`; `ProofSoundAtDesc`.
-/
def ProofSoundAtRuns : Prop :=
  RowFit (DP.at a) L₁ L₂ → PubEarly Kc early F.pub →
  (∀ rec, ((linksP Kc DP tFp tJp t3p L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F) S).comap
    fun x : Kc.conf.X => (x, rec)).KnowsJ N k₁ k₂) →
  TieGlue Kc early drop put →
  TieOnOk Kc DP tFp tJp t3p silP F.run early L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F) S →
  TieTells Kc DP tFp tJp t3p L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F) S put tokW toW →
  FirstHolds Kc DP tFp tJp t3p L₁ L₂ (descRun₁ F) (descRun₂ F) (descRun₃ F) S tokW
    (fun x₁ => H.heard x₁.2) →
  Err.Below S.ε₁ U.εs → Err.Below S.ε₂ U.εs → Err.Below S.ε₃ U.εs →
  CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                                             eL N early none) P T U)

end VerifiableInference.OnPublicFiles
