-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyPaid.lean: `KeySoundOfBlocks` (Johnson/Desc/Sound/KeyRule.lean) WITH TEN OF
ITS PREMISES GONE: what is left to be shown for the key file's named hypothesis on soundness.

What is paid, and how.
  `lang`: by `keyLangIs` (Johnson/Desc/Sound/KeyLang.lean): the first condition and the first
    relation are written: "no collision at the record's seed"; "decodes with the record".
  `Three.Glued` (three clauses): the relation at a chain's last boundary is WRITTEN as what the next
    chain claims, at its first boundary, of what this chain hands on; the last chain's is "true"
    (`Three.endsOf`, `glued_endsOf`). No claim is dropped by that: the last block of a chain then
    owes goodness into that relation.
  the three laws on the silent rounds' tests: the row's three tests are laid as "yes". These three
    stand in the row of the analysis alone: the verifier of which the conclusion speaks keeps the
    file's own test on the silent rounds (`silK`).
  `h₁`, `h₂`, `h₃`: from `Three.Fits` and `shapeIsChain`.
What is left (`KeySoundShort`): the reader of the instance; `Three.Fits`; `EachGood` at each of the
three chains; `RowFit`; the errors' size.

Main names: `Three.last₁`, `Three.last₂`, `Three.endsOf`, `glued_endsOf`; `Three.Fits.shape₁` (₂,
₃); `Three.keyPlaces`; `KeySoundShort`, `keySoundShort`.
Trials: `endsOf_last₁`, `endsOf_last₂`: what the written relations say, as equivalences: they are
"true" only where the next chain's first relation is.

Limits: those of KeyRule.lean: a rule; no block is shown good here, and nothing bounds an error.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyLang
import Johnson.Desc.Sound.ChainRuleProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Iop.Reduction (orOff)
open _root_.TypedOracleCompiler.Joined (Links row_sound)

/-! ## 1 The relations at the chains' ends -/

section Ends
variable {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type}

/-- What the second chain claims, at its first boundary, of what the first chain hands on. -/
def Three.last₁ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    S₁ × (EAll D all).Str → W → Prop := fun b w => ∃ x, T.mid₁ Q (T.out₁ x b.1, b.2) w

/-- What the third chain claims, at its first boundary, of what the second chain hands on. -/
def Three.last₂ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    S₂ × (EAll D all).Str → W → Prop := fun b w => ∃ x, T.mid₂ Q (T.out₂ x b.1, b.2) w

/-- **The relations at the three chains' last boundaries, written.** At the first chain's: what the
second chain claims at its first boundary of what the first chain hands on (at some instance: in the
filling that is meant what is handed on does not read the instance). At the second chain's: the
third chain has a first record, and what it claims there. At the third chain's: "true". The
conditions there hold of all statements: a statement outside the next chain's first condition counts
as having every witness (`Three.mid₁`, `Three.mid₂`). All other boundaries as they were. -/
def Three.endsOf (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W) :
    Places D all S₁ S₂ S₃ W where
  on₁ := fun i => if i = 1 + T.l₁.length then fun _ => True else Q.on₁ i
  R₁ := fun i => if i = 1 + T.l₁.length then T.last₁ Q else Q.R₁ i
  on₂ := fun i => if i = 1 + T.l₂.length then fun _ => True else Q.on₂ i
  R₂ := fun i => if i = 1 + T.l₂.length then T.last₂ Q else Q.R₂ i
  on₃ := fun i => if i = 1 + T.l₃.length then fun _ => True else Q.on₃ i
  R₃ := fun i => if i = 1 + T.l₃.length then fun _ _ => True else Q.R₃ i

variable (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)

theorem endsOf_on₁_zero : (T.endsOf Q).on₁ 0 = Q.on₁ 0 := by
  unfold Three.endsOf
  dsimp only
  exact if_neg (by omega)
theorem endsOf_R₁_zero : (T.endsOf Q).R₁ 0 = Q.R₁ 0 := by
  unfold Three.endsOf
  dsimp only
  exact if_neg (by omega)
theorem endsOf_on₂_zero : (T.endsOf Q).on₂ 0 = Q.on₂ 0 := by
  unfold Three.endsOf
  dsimp only
  exact if_neg (by omega)
theorem endsOf_R₂_zero : (T.endsOf Q).R₂ 0 = Q.R₂ 0 := by
  unfold Three.endsOf
  dsimp only
  exact if_neg (by omega)
theorem endsOf_on₃_zero : (T.endsOf Q).on₃ 0 = Q.on₃ 0 := by
  unfold Three.endsOf
  dsimp only
  exact if_neg (by omega)
theorem endsOf_R₃_zero : (T.endsOf Q).R₃ 0 = Q.R₃ 0 := by
  unfold Three.endsOf
  dsimp only
  exact if_neg (by omega)
theorem endsOf_R₁_last : (T.endsOf Q).R₁ (1 + T.l₁.length) = T.last₁ Q := by
  unfold Three.endsOf
  dsimp only
  exact if_pos rfl
theorem endsOf_R₂_last : (T.endsOf Q).R₂ (1 + T.l₂.length) = T.last₂ Q := by
  unfold Three.endsOf
  dsimp only
  exact if_pos rfl
theorem endsOf_R₃_last : (T.endsOf Q).R₃ (1 + T.l₃.length) = fun _ _ => True := by
  unfold Three.endsOf
  dsimp only
  exact if_pos rfl

/-- What the next chain claims is read at first boundaries, which are as they were. -/
theorem mid₁_endsOf : T.mid₁ (T.endsOf Q) = T.mid₁ Q := by
  unfold Three.mid₁
  rw [endsOf_on₂_zero, endsOf_R₂_zero]

theorem mid₂_endsOf : T.mid₂ (T.endsOf Q) = T.mid₂ Q := by
  unfold Three.mid₂
  rw [endsOf_on₃_zero, endsOf_R₃_zero]

/-- What the written relation at the first chain's end says. -/
theorem endsOf_last₁ (b : S₁ × (EAll D all).Str) (w : W) :
    (T.endsOf Q).R₁ (1 + T.l₁.length) b w ↔
      ∃ x, Q.R₂ 0 (T.in₂ (T.out₁ x b.1), b.2) w ∨ ¬ Q.on₂ 0 (T.in₂ (T.out₁ x b.1), b.2) := by
  rw [endsOf_R₁_last]
  exact Iff.rfl

/-- What the written relation at the second chain's end says. -/
theorem endsOf_last₂ (b : S₂ × (EAll D all).Str) (w : W) :
    (T.endsOf Q).R₂ (1 + T.l₂.length) b w ↔
      ∃ x s, T.in₃ (T.out₂ x b.1) = some s ∧ (Q.R₃ 0 (s, b.2) w ∨ ¬ Q.on₃ 0 (s, b.2)) := by
  rw [endsOf_R₂_last]
  exact Iff.rfl

/-- **At the written relations the chains' ends fit together.** -/
theorem glued_endsOf : T.Glued (T.endsOf Q) where
  glue₁ := by
    intro x b w h
    rw [mid₁_endsOf] at h
    refine Or.inl ?_
    rw [endsOf_R₁_last]
    exact ⟨x, h⟩
  glue₂ := by
    intro x b w h
    rw [mid₂_endsOf] at h
    refine Or.inl ?_
    rw [endsOf_R₂_last]
    exact ⟨x, h⟩
  ends := by
    intro x b _
    refine Or.inl ?_
    rw [endsOf_R₃_last]
    trivial

variable {T}

/-- The pieces' lists of rounds, appended, are the chain's. -/
theorem Three.Fits.shape₁ (hf : T.Fits) : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁ :=
  (shapeIsChain _ _ _ _ _ T.p₁ T.l₁).trans (congrArg (uLT C) hf.data₁)
theorem Three.Fits.shape₂ (hf : T.Fits) : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂ :=
  (shapeIsChain _ _ _ _ _ T.p₂ T.l₂).trans (congrArg (uLT C) hf.data₂)
theorem Three.Fits.shape₃ (hf : T.Fits) : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃ :=
  (shapeIsChain _ _ _ _ _ T.p₃ T.l₃).trans (congrArg (uLT C) hf.data₃)

end Ends

/-! ## 2 The key file -/

/-- **The key file's conditions and relations**: Q's, with the first condition and the first
relation of Johnson/Desc/Sound/KeyLang.lean at the first boundary and the written relations at the
three chains' ends. -/
def Three.keyPlaces {a : ℕ} (Kc : ConfLetters a) {DK : WholeD} {all : List LeftT}
    {S₁ S₂ S₃ X₁ X₂ Cl W : Type}
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec) :
    Places (DK.at a) all S₁ S₂ S₃ W :=
  T.endsOf (Q.keyFirst Kc rd)

/-- The row's test on what a silent round sends: yes. -/
abbrev yes₂ {α β : Type} : α → β → Bool := fun _ _ => true

/-- **The key file's hypothesis on soundness, from what is left.** -/
def KeySoundShort : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK DP : WholeD) (TFk TJk T3k TFp TJp T3p : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
    (runP : Kc.conf.X × Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
    (all : List LeftT) (S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec)
    (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK (runRow T.run₁ T.run₂ T.run₃) silP
      runP eL N early late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                      (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                       (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (hf : T.Fits),
    (∀ rec, rd (T.in₁ rec) = rec) →
    EachGood (T.keyPlaces Kc Q rd).on₁ (T.keyPlaces Kc Q rd).R₁ 0 (T.p₁ :: T.l₁) →
    EachGood (T.keyPlaces Kc Q rd).on₂ (T.keyPlaces Kc Q rd).R₂ 0 (T.p₂ :: T.l₂) →
    EachGood (T.keyPlaces Kc Q rd).on₃ (T.keyPlaces Kc Q rd).R₃ 0 (T.p₃ :: T.l₃) →
    RowFit (DK.at a) all all →
    Err.Below (Err.timesShared (2 ^ Tl.W.depthReqT) (chainsOf (ckP .two) (DK.at a) tFk tJk t3k).ann
      ((T.row tFk tJk t3k yes₂ yes₂ yes₂).links
        (T.snd tFk tJk t3k (T.keyPlaces Kc Q rd) yes₂ yes₂ yes₂ hf.shape₁ hf.shape₂
          hf.shape₃)).err) U.εs →
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P Tl U)

theorem keySoundShort : KeySoundShort := by
  intro a Kc DK DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP eL N early late
    all S₁ S₂ S₃ X₁ X₂ Cl W T Q rd P Tl U hf hrd g₁ g₂ g₃ hfit below
  exact keySoundOfBlocks a Kc DK DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP
    eL N early late all S₁ S₂ S₃ X₁ X₂ Cl W T (T.keyPlaces Kc Q rd) yes₂ yes₂ yes₂ hf.shape₁
    hf.shape₂ hf.shape₃ P Tl U hf g₁ g₂ g₃ (glued_endsOf T _) hfit
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (LangIs.congr Kc (keyLangIs Kc T Q rd hrd) (endsOf_on₁_zero T _)
      (endsOf_R₁_zero T _)).langAt below

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.endsOf_last₁
#print axioms VerifiableInference.Desc.Sound.endsOf_last₂
#print axioms VerifiableInference.Desc.Sound.glued_endsOf
#print axioms VerifiableInference.Desc.Sound.keySoundShort
