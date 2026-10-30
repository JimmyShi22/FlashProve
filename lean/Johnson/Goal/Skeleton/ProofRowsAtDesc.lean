-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Skeleton/ProofRowsAtDesc.lean: the seven fields of `VerifierAndGoals.AtTheName.RowsOfProofFile`
(Johnson/Goal/Skeleton/ProofFile.lean), AT A DESCRIPTION's OWN PLAIN FILE, from the premises of
`proofSound_at_descB` (Johnson/Desc/Plain/BothAtDesc.lean).

Why. What is owed of the proof file is one structure of seven fields over free letters, among them a
`PlainFile`. The laws that the kinds' files prove speak of a description's blocks.
`proofSound_at_descB` takes such laws to `CompilerSoundnessConditionStatements.proofSound` in one call of the rule whose
premises the seven fields are. Here that call's arguments are handed out as the structure's fields:
so a law on blocks ends at a field.
  `lettersAtDescB`: the letters: the fixed witness w₀; P := `plainP …`
  (Johnson/Desc/Plain/AtDesc.lean): the description's own three folds, with the conditions and
  relations Pl, what is known M and the claims L₁ L₂; the key of what the first chain hands on: `key
  0` at the shared chain's start; that key as a function F₁ of the record and the stored table.
  `rows_at_descB`: the seven fields at these letters. The three chains' by `fold_three_chainsB`;
  `yes_gives_the_chains` and `tie` by `decides_at_desc` and `ties_of_tie`
  (Johnson/Desc/Plain/BothAtDescSteps.lean); `proof_below` from three bounds.
  `proofSound_of_rows_at_descB`: the ring closed: the seven fields, handed to
  `VerifierAndGoals.AtTheName.proofSound_of_rows`, give `proofSound_at_descB`'s own conclusion again: the
  repackaging loses nothing.
Limits. A REPACKAGING: no new reasoning; nothing is paid. The premises are those of
`proofSound_at_descB`, to the letter (by program); none is shown of a description of the protocol.
NO MEMBER. At the frame `filesOf Kc …`, not yet at the name's record. No soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Skeleton.ProofFile
import Johnson.Desc.Plain.BothAtDescSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc worst_le)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (F : FileDescription (Kc.conf.X × Kc.conf.Rec)) (all : List LeftT) {X₁ X₂ W κ : Type}
  (T : ThreeAt (ckP .two) (DP.at a) all F X₁ X₂ W)
  (Pl : PPlaces (DP.at a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at a) all).Str → κ)

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **The letters at a description's own plain file.** -/
def lettersAtDescB (w₀ : Kc.conf.Cells)
    (F₁ : Kc.conf.Rec → (oneExternalString (2 ^ (DP.at a).a) SgX).Str → κ) :
    VerifierAndGoals.AtTheName.ProofLetters
      (innerInputOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                       none) P Tl)
      (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P Tl U)
      (chainsOf (ckP .two) (DP.at a) tFp tJp t3p) where
  w₀ := w₀
  P := plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d
  κ₁ := κ
  k₁ := fun b => key 0 ((atDesc F T).in₂ b.1, b.2)
  F₁ := F₁

/-- **The seven fields, from the premises of `proofSound_at_descB`.** -/
theorem rows_at_descB (w₀ : Kc.conf.Cells) (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (fit : RowFit (DP.at a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (F₁ : Kc.conf.Rec → (oneExternalString (2 ^ (DP.at a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F T).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at a).ds₃ h₃) U.εs) :
    VerifierAndGoals.AtTheName.RowsOfProofFile
      (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run)
      (lettersAtDescB Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N early F all T Pl h₁ h₂
        h₃ M L₁ L₂ d key P Tl U w₀ F₁) U.εs where
  first_chain_knows_means :=
    (fold_three_chainsB tFp tJp t3p _ _ _ h₁ h₂ h₃ d key hf e₁ e₂ e₃ G).l₁
  shared_joint_count := (fold_three_chainsB tFp tJp t3p _ _ _ h₁ h₂ h₃ d key hf e₁ e₂ e₃ G).l₂
  leads3_last_chains_table :=
    (fold_three_chainsB tFp tJp t3p _ _ _ h₁ h₂ h₃ d key hf e₁ e₂ e₃ G).l₃
  shared_start_is_the_records := oneKey
  yes_gives_the_chains :=
    decides_at_desc Kc DP tFp tJp t3p silP early F all T Pl h₁ h₂ h₃ M L₁ L₂ d hO fit pubEarly
  tie := ties_of_tie Kc DP tFp tJp t3p silP early F all T Pl h₁ h₂ h₃ M L₁ L₂ d w₀ hO fit pubEarly
    tie
  proof_below := max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₁⟩))
    (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₂⟩))
      (worst_le (show Err.Below _ U.εs from ⟨by simp, b₃⟩)))

/-- **The ring closed**: the seven fields give `proofSound_at_descB`'s own conclusion again. -/
theorem proofSound_of_rows_at_descB (w₀ : Kc.conf.Cells)
    (F₁ : Kc.conf.Rec → (oneExternalString (2 ^ (DP.at a).a) SgX).Str → κ)
    (R : VerifierAndGoals.AtTheName.RowsOfProofFile
      (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run)
      (lettersAtDescB Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP eL N early F all T Pl h₁ h₂
        h₃ M L₁ L₂ d key P Tl U w₀ F₁) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                                               F.run eL N early none) P Tl U) :=
  VerifierAndGoals.AtTheName.proofSound_of_rows (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run) rfl
    rfl rfl _ U.εs rfl R

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rows_at_descB
#print axioms VerifiableInference.OnPublicFiles.proofSound_of_rows_at_descB
