-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfDesc.lean: the proof file's named hypothesis on soundness
(`CompilerSoundnessConditionStatements.proofSound`, Johnson/Top/InnerCompiledVerifier.lean) at the three protocols of `filesOf`, WHERE THE
PROOF FILE's DECISION IS A DESCRIPTION's (`FileDescription.run`, Johnson/Desc/Block.lean). A SHEET OF
STATEMENTS: propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE (the proofs:
Johnson/Flat/ProofOfDescProofs.lean).

Why. Johnson/Flat/ProofOfRow.lean has the hypothesis from eight premises at a decision that is a
letter; Johnson/Flat/TiesSheet.lean cuts the premise in which the meaning sits (`RowTies`) into
five; Johnson/Flat/TiesAtDesc.lean has one of the five (`TieFins`) at a description. Here they are
joined: what is left to show of a description F, by name, in one list.

The letters: those of the three sheets.

Main names.
  `RowTiesAtDesc`: `RowTies` at runP := F.run.
  `ProofSoundAtDesc`: the hypothesis at runP := F.run. ITS PREMISES, ALL NAMED:
    ON F's TEXT ALONE: gives · kept · ends (readings of `FileDescription.runEnd`; kept also wants that
    `early`
      keeps F's public part) · H : `F.Hears` (the reply's block lays what it hears; no later block
      turns it; the last test compares it with what is asked).
    ON THE DATA: fit (a test with code) · three bounds on the chains' errors.
    ON THE INSTANCES: glue (what `early` drops, put back, gives the instance).
    THE CHAINS' CLAUSES: knows · reads (the first chain's extractor yields the token that the
      transcript names) · onOk · tells (what the first relation says).

Every "there is", walked. As in the three sheets; none is new here.

Limits. Those of the three sheets. NO DESCRIPTION OF THE PROTOCOL IS LAID IN, and the three runs are
still letters beside F: that they are F's own three folds is what gives, kept and ends are to be
shown of. A description that never says yes meets gives, ends, onOk and H.fins for nothing, and the
conclusion then holds of a verifier that refuses all. THE MEANING SITS IN knows WITH tells: at a
first relation that holds of everything knows is free and tells asks the object's relation outright.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TiesAtDesc

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

/-- **`RowTies` at a description's decision.** Meant by: `RowDecides`; `ReadsOfFirst`;
`TieFinsAtDesc`; `TiesOfFive`. -/
def RowTiesAtDesc : Prop :=
  RowFit (DP.at a) L₁ L₂ → RunGives Kc F.run run₁ run₂ run₃ → EarlyKept Kc early run₁ →
  EndsOfRun F → TieGlue Kc early drop put →
  TieOnOk Kc DP tFp tJp t3p silP F.run early L₁ L₂ run₁ run₂ run₃ S →
  TieTells Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S put tokW toW →
  FirstReads Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S tokW (saidP₁ Kc DP tFp tJp t3p F drop rd H) →
  RowTies Kc DP tFp tJp t3p silP F.run early L₁ L₂ run₁ run₂ run₃ S toW

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (T : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)
  {κ₁ κ₂ : Type} (k₁ : X₁ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₁.Str → κ₁)
  (k₂ : X₂ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₂.Str → κ₂)

/-- **The proof file's named hypothesis on soundness, at a description's decision.** Meant by:
`RowTiesAtDesc`; `ProofSoundOfRow`. -/
def ProofSoundAtDesc : Prop :=
  RowFit (DP.at a) L₁ L₂ → RunGives Kc F.run run₁ run₂ run₃ → EarlyKept Kc early run₁ →
  EndsOfRun F →
  (∀ rec, ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).comap
    fun x : Kc.conf.X => (x, rec)).KnowsJ N k₁ k₂) →
  TieGlue Kc early drop put →
  TieOnOk Kc DP tFp tJp t3p silP F.run early L₁ L₂ run₁ run₂ run₃ S →
  TieTells Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S put tokW toW →
  FirstReads Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S tokW (saidP₁ Kc DP tFp tJp t3p F drop rd H) →
  Err.Below S.ε₁ U.εs → Err.Below S.ε₂ U.εs → Err.Below S.ε₃ U.εs →
  CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                                             eL N early none) P T U)

end VerifiableInference.OnPublicFiles
