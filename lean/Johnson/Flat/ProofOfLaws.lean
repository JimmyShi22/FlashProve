-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfLaws.lean: THE PROOF FILE's NAMED HYPOTHESIS ON SOUNDNESS
(`CompilerSoundnessConditionStatements.proofSound`), WHERE THE PROOF FILE's DECISION IS A DESCRIPTION's (`FileDescription.run`), FROM
ONE LAW A BLOCK AND A SHORT LIST OF NAMED FACTS. One statement, written as `def … : Prop`. NOTHING
IS PROVED IN THIS FILE (the proof: Johnson/Flat/ProofOfLawsProofs.lean).

Why. Johnson/Flat/ProofOfBlocks.lean still asks `knows` (the list `Links.KnowsJ`, record by record),
`TieOnOk` and `TieTells`. The first is the conclusion of the rule of composition for N slots behind
one key (`FoldSlots`, Johnson/Desc/Sound/FoldSlots.lean), at a NAMED key; the other two are had at
the filling that is meant (Johnson/Flat/TellsAtBlocks.lean). Here all are laid in.

`ProofSoundOfLaws`: WHAT IS LEFT, COUNTED: twenty-two.
  THE LAST TEST. 0 finGives: the description's last test's yes gives g's, a test on the public part
    and the three ends: g STANDS IN THE ROW (`atDescFin F g T`, Johnson/Desc/Sound/DescFin.lean), so
    that 6 asks, at the third chain's end, the last relation only WHERE g SAYS YES. Free at g :=
    "yes always".
  THE PIECES. 1 ofDesc: they hold F's own blocks. 2 fits: their stretches are the file's three
    chains.
  ONE LAW A BLOCK. 3, 5 the first and the third chain: each block is good for one statement, at its
    own errors (`EachGood`). 4 THE SHARED CHAIN: each block has its law for N slots in two parts
    (`EachLostBoth`): its own error bears what hangs on what the slots share ONCE and what hangs on
    a slot's own statement N TIMES. 6 glued: the relations at the chains' ends fit together.
  THE REPLY. 7 H : `F.Hears`: the reply's block lays what it hears; no later block turns it; the
    last test compares it with what is asked. 8 exts (`ExtRowAt`): in front of the reply's block
    each extractor hands the token on; the reply's block's sets it.
  THE FIRST BOUNDARY, AT FIRST STATEMENTS ALONE (the first record that an instance's public part
    gives; a stored table; no tree sent). 9 its condition holds there, at every instance that passes
    the description's test on the instance AND EVERY STORED TABLE THAT DECODES WITH THE RECORD (so
    the condition may hold that promise and hand it on). 10 its relation there gives `firstRel` at
    what back reads off the public part: HERE THE MEANING ENTERS.
  THE INSTANCES. 11 pubEarly. 12 pubKeeps. 13 putEarly. 14 glue. 15 ONE KEY: the shared chain's
    first record is a function s₂ of the record alone.
  THE DATA. 16 fit (`RowFit`). 17 the shared chain opens no tree of the first chain. Both are tests.
  THE NUMBERS. 18, 19, 20 the three chains' blocks' errors appended are shares of at most U.εs. THE
    SHARED CHAIN's STAND WITH NO FACTOR N: the factor is inside 4, at the terms that need it.
  (21: the letters' own types: T, Q and the three equations of shapes h₁, h₂, h₃: free by
    `ShapeIsChain` with 2.)

Every "there is", walked. None of its own. `Piece.LostBoth` has one (the split of a block's errors
and the two properties): FoldSlots.lean's head walks it.

Limits. A RULE: NO DESCRIPTION OF THE PROTOCOL IS LAID IN, NO BLOCK OF THE PROTOCOL MEETS A PREMISE.
A MEMBER OF ALL PREMISES TOGETHER: a toy's, at which no error is spent: Johnson/Flat/LawsToy.lean
[not in this library].
Those of ProofOfBlocks.lean, FoldSlots.lean and TellsAtBlocks.lean. A description that refuses all
meets every premise on the blocks for nothing. THE ROW IS STILL LAXER THAN THE DECISION: the three
runs hold neither the tests on the plan nor the test on the instance (9 spends the latter), and of
the last test just g: what of it reads the instance beyond the public part is spent in 7 (the asked
reply) or not at all.
THE TYPE Tok: the element as it is written:
Johnson/Flat/TiesAtReqE.lean [not in this library] says why. Nothing says that U.εs is small. Only
late = none. Nothing on
acceptance, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TellsAtBlocks

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
  (ThreeAt PlacesAt atDesc atDescFin FinGives OfDesc ExtRowAt rowIOR EAll EachGood
  EachLostBoth actsOf)

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
  (back : F.XiPub → Kc.conf.X × Kc.conf.Rec) (s₂ : Kc.conf.Rec → F.S₂)
  (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **The proof file's named hypothesis on soundness, at a description's decision, from one law a
block.** Meant by: `foldSlots` (Johnson/Desc/Sound/FoldSlotsProofs.lean); `onOkAtBlocks`,
`tellsAtBlocks` (Johnson/Flat/TellsAtBlocks.lean); `proofSoundOfBlocks`
(Johnson/Flat/ProofOfBlocksProofs.lean). -/
def ProofSoundOfLaws : Prop :=
  OfDesc F T → FinGives F g → (atDescFin F g T).Fits →
  EachGood Q.on₁ Q.R₁ 0 ((atDescFin F g T).p₁ :: (atDescFin F g T).l₁) →
  EachLostBoth N Q.on₂ Q.R₂ (actsOf Prod.snd (DP.at a).t₁ (atDescFin F g T).p₂ (atDescFin F g T).l₂)
    0
    ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂) →
  EachGood Q.on₃ Q.R₃ 0 ((atDescFin F g T).p₃ :: (atDescFin F g T).l₃) →
  (atDescFin F g T).Glued Q →
  ExtRowAt tok rd H.pre.length (atDescFin F g T).p₁ (atDescFin F g T).l₁ →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str), F.okStart x = true →
    Kc.conf.D y x.2 ≠ none → Q.on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => []))) →
  (∀ (x : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str) (w : W),
    Q.R₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])) w →
    firstRel Kc DP put tok toW (back (F.pub x), y) w) →
  PubEarly Kc early F.pub → PubKeeps Kc early F.pub back → PutEarly Kc early put →
  TieGlue Kc early drop put →
  (∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec) →
  RowFit (DP.at a) all all →
  (∀ d ∈ (DP.at a).ds₂, ∀ j ∈ d.opens, (DP.at a).t₁ ≤ j) →
  Err.Below (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃).ε₁ U.εs →
  Err.Below (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃).ε₂ U.εs →
  Err.Below (sndB Kc DP tFp tJp t3p F all T g Q h₁ h₂ h₃).ε₃ U.εs →
  CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                                             eL N early none) P Tl U)

end VerifiableInference.OnPublicFiles
