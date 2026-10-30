-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfBlocks.lean: the proof file's named hypothesis on soundness
(`CompilerSoundnessConditionStatements.proofSound`) where the proof file's decision is a description's (`FileDescription.run`), AT THE
RULE OF COMPOSITION's VALUE (`atDesc F T`, Johnson/Desc/Sound/DescThree.lean: the pieces hold the
description's own blocks; `Three.snd`, Johnson/Desc/Sound/FileRule.lean: the relations at the
boundaries, the blocks' extractors composed, the blocks' errors appended). One definition and one
statement, written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE (the proof:
Johnson/Flat/ProofOfBlocksProofs.lean).

Why. Johnson/Flat/ProofOfDescRuns.lean leaves S (the relations, extractors and errors) a letter, and
asks of it `FirstHolds`. At the rule of composition's value that law follows from one law a block
(Johnson/Desc/Sound/ExtHeard.lean). Here the two are joined: the proof file's sibling of
`KeySoundOfBlocks` (Johnson/Desc/Sound/KeyRule.lean), at the description's own decision.

Main names.
  `sndB`: `Three.snd` at `atDesc F T`, the row's three tests on the silent rounds saying yes always.
  `ProofSoundOfBlocks`: THE HYPOTHESIS AT runP := F.run. WHAT IS LEFT, ALL NAMED:
    THE PIECES: ofDesc (they hold F's own blocks) · fits (their stretches are the file's three
    chains). THE DATA: fit (a test with code) · three bounds on the blocks' errors appended.
    THE INSTANCES: pubEarly · glue.
    F's TEXT: H : `F.Hears`: the reply's block lays what it hears; no later block turns it; the last
    test
      compares it with what is asked.
    THE EXTRACTORS: exts (`ExtRowAt`): in front of the reply's block each block's extractor hands
    the
      token on; the reply's block's extractor sets it to what rd reads of its rounds.
    THE CLAUSES: knows (`KnowsJ`, record by record) · onOk · tells (what the relation at the first
      boundary says).

THE ENDS' PART OF THE LAST TEST STANDS IN THE ROW: the value is `atDescFin F g T`
(Johnson/Desc/Sound/DescFin.lean): g: a test on the public part and the three ends, which the
description's last test's yes gives (`FinGives`). At g := "yes always" it is `atDesc F T`, and
`FinGives` is free.

Every "there is", walked. None is new here.

Limits. Those of ProofOfDesc.lean, ExtHeard.lean, DescThree.lean and FileRule.lean. NO DESCRIPTION
OF THE PROTOCOL IS LAID IN, and no piece. `knows` is still a premise: from the blocks' goodness:
`FileKnowsJOfGood` (Johnson/Desc/Sound/FileBatch.lean), which is at instances with the record fixed.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfDesc
import Johnson.Flat.TiesFilling
import Johnson.Desc.Sound.DescFin
import Johnson.Desc.Sound.ExtHeard

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
  (ThreeAt PlacesAt atDesc atDescFin FinGives OfDesc ExtRowAt rowIOR)

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

/-- The rule of composition's relations, extractors and errors at the description's pieces, as the
letters S of Johnson/Flat/ProofOfRow.lean. -/
abbrev sndB : (rowP Kc DP tFp tJp t3p all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
    (atDescFin F g T).run₃).Snd :=
  (atDescFin F g T).snd tFp tJp t3p Q (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁ h₂ h₃

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

/-- **The proof file's named hypothesis on soundness, at a description's decision, from its
blocks.** Meant by: `runsAtDesc`, `runGivesRowAt` (Johnson/Desc/Sound/DescThreeProofs.lean);
`keptAt`, `heardAt`, `endsAt` (Johnson/Flat/ProofOfDescRunsProofs.lean); `hearsRowOf`,
`firstHoldsAt` (Johnson/Desc/Sound/ExtHeardProofs.lean); `readsOfHolds`; `proofSoundAtDesc`. -/
def ProofSoundOfBlocks : Prop :=
  OfDesc F T → FinGives F g → (atDescFin F g T).Fits → RowFit (DP.at a) all all → PubEarly Kc early
    F.pub →
  (∀ rec, ((linksP Kc DP tFp tJp t3p all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
  (atDescFin F g T).run₃
    (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃)).comap fun x : Kc.conf.X => (x, rec)).KnowsJ N k₁
      k₂) →
  TieGlue Kc early drop put →
  TieOnOk Kc DP tFp tJp t3p silP F.run early all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
    (atDescFin F g T).run₃ (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃) →
  TieTells Kc DP tFp tJp t3p all all (atDescFin F g T).run₁ (atDescFin F g T).run₂
    (atDescFin F g T).run₃
    (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃) put tok toW →
  ExtRowAt tok rd H.pre.length (atDescFin F g T).p₁ (atDescFin F g T).l₁ →
  Err.Below (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃).ε₁ U.εs →
  Err.Below (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃).ε₂ U.εs →
  Err.Below (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃).ε₃ U.εs →
  CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                                             eL N early none) P Tl U)

end VerifiableInference.OnPublicFiles
