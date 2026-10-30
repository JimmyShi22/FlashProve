-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/KeyRule.lean: THE KEY FILE: its named hypothesis on soundness
(`CompilerSoundnessConditionStatements.keySound`, Johnson/Top/InnerCompiledVerifier.lean), from the goodness of the blocks of its three
chains: one statement, `KeySoundOfBlocks`, and its proof.

The setting. A key file has three hash chains like a proof file, and serves one request. Its
hypothesis asks that its protocol be round-by-round sound for the language "the stored table has a
collision at the record's seed, or decodes with the record", every round's error (a shared round's
counted once for each leaf of the call's request tree) being a share of at most εs. The library has:
from `Links.Knows` and "where the file's verifier says yes the three reductions put out", the file's
protocol is round-by-round sound for the language of the first relation, at the three chains' errors
in a row (`row_sound`, OnBytes/TypedOracleCompiler/Joined/Top.lean). Johnson/Desc/Sound/FileRule.lean has both
premises at the three folds (`FileKnows`, `FileDecides`).

What is said. At the three protocols of `filesOf` (Johnson/EntryRec/AtFiles.lean) whose key file's
decision is the three folds in a row: if the three rows of pieces are the key file's three chains,
every block is good, the relations at the chains' ends fit together, the data and the list of trees
fit (`RowFit`), the silent rounds' tests follow from the file's, the first relation's language lies
in the hypothesis' language (`lang`), and the errors are small (`below`): `CompilerSoundnessConditionStatements.keySound`.

Limits: those of FileRule.lean: a rule, whose premises are met by no block here. `lang` and `below`
are premises: what the first relation says, and how large the blocks' errors are, is not looked at.
That a key file's `FileDescription.run` is the three folds in a row is owed where it is made. As in
FileRule.lean, goodness of a block of the second chain is asked at the block's own relation AND
whatever claim is carried past that chain.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileKnowsProof
import Johnson.Desc.Sound.FileDecidesProof
import Johnson.Flat.InnerInputOfThreeProtocols

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.TypedOracleCompiler.Joined (Links row_sound)

/-- **The key file's hypothesis on soundness, from its blocks.** -/
def KeySoundOfBlocks : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK DP : WholeD) (TFk TJk T3k TFp TJp T3p : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
    (runP : Kc.conf.X × Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
    (all : List LeftT) (S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (okF : Kc.conf.Rec → TFk → Bool)
    (okJ : X₁ → TJk → Bool) (ok3 : X₂ → T3k → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT (ckP .two) (DK.at a).ds₁)
    (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT (ckP .two) (DK.at a).ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT (ckP .two) (DK.at a).ds₃)
    (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK (runRow T.run₁ T.run₂ T.run₃) silP
      runP eL N early late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                      (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                       (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P),
    T.Fits → EachGood Q.on₁ Q.R₁ 0 (T.p₁ :: T.l₁) → EachGood Q.on₂ Q.R₂ 0 (T.p₂ :: T.l₂) →
    EachGood Q.on₃ Q.R₃ 0 (T.p₃ :: T.l₃) → T.Glued Q →
    RowFit (DK.at a) all all →
    (∀ x u v c, silK x u v c = true → okF x u = true) →
    (∀ x u v c vw x₁, silK x u v c = true → T.run₁ x vw = some x₁ → okJ x₁ v = true) →
    (∀ x u v c vw vw' x₁ x₂, silK x u v c = true → T.run₁ x vw = some x₁ →
      T.run₂ x₁ vw' = some x₂ → ok3 x₂ c = true) →
    (∀ rec y, (Q.on₁ 0 (T.in₁ rec, (y, fun _ => [])) →
        ∃ w, Q.R₁ 0 (T.in₁ rec, (y, fun _ => [])) w) →
      Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none) →
    Err.Below (Err.timesShared (2 ^ Tl.W.depthReqT) (chainsOf (ckP .two) (DK.at a) tFk tJk t3k).ann
      ((T.row tFk tJk t3k okF okJ ok3).links
        (T.snd tFk tJk t3k Q okF okJ ok3 h₁ h₂ h₃)).err) U.εs →
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P Tl U)

theorem keySoundOfBlocks : KeySoundOfBlocks := by
  intro a Kc DK DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP eL N early late
    all S₁ S₂ S₃ X₁ X₂ Cl W T Q okF okJ ok3 h₁ h₂ h₃ P Tl U hf g₁ g₂ g₃ hgl hfit hF hJ h3 lang below
  have hk := fileKnows (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W TFk TJk T3k tFk tJk
    t3k T Q okF okJ ok3 h₁ h₂ h₃ hf g₁ g₂ g₃ hgl
  have hd := fileDecides (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W TFk TJk T3k tFk
    tJk t3k T okF okJ ok3 silK (T.snd tFk tJk t3k Q okF okJ ok3 h₁ h₂ h₃) hfit hF hJ h3
  have hs := row_sound (wholeDesc (ckP .two) (DK.at a) tFk tJk t3k silK
    (runRow T.run₁ T.run₂ T.run₃)) hk (fun x y τ hacc => by
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hacc
      cases u
      exact hd x y τ hu)
  exact ⟨_, below, fun rec y hL => hs rec y fun h => hL (lang rec y h)⟩

end VerifiableInference.Desc.Sound
