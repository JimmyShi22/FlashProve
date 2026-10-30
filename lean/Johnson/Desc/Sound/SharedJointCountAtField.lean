-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountAtField.lean: **THE ROW shared_joint_count ENDS AT ITS FIELD.** Statements; each proof is calls of what lies.

THE FIELD (Johnson/Goal/Skeleton/ProofFile.lean; = the second premise of Leads3B, Johnson/Desc/Plain/BothAtDesc.lean:100):
  shared_joint_count : L.P.K₂.LeadsBN L.k₁ L.P.on₁ (fun c d => L.P.on₂ d ∧ (L.P.L₂ d → L.P.L₁ c)) r.protocol.maxBatchSize L.P.ε₂.
THE LETTERS (one choice for the proof file's letters): L.P := plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d · L.k₁ c := key 0 ((atDesc F T).in₂ c.1, c.2), key := keyAt Prod.snd
(DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂.
  field_of_laws   from the last clause of every form of the row here (EachLawsBN at that key, at Pl.on₂ | Pl.Q₂, for N slots): THE FIELD's TYPE, TO THE LETTER, at these letters. By the keys by make
                  (KeysByMake.lean) and file_leadsBN₂ (BothAtDesc.lean:183).
  field_of_rowE   from the row's fifth form (SharedJointCountRowE.lean), where the places' second parts ARE the table's terms: Pl.on₂ = onQ₂ …, Pl.Q₂ = stepAt … (two equations, premises).
                  The sixth and seventh forms give the fifth (rowG_gives_E · rowH_gives_E).
  leads3B_of_three   THAT field_of_laws' CONCLUSION IS THE FIELD's TYPE IS HELD BY LEAN: the constructor of Leads3B takes it as its second field, at these letters.
PREMISES BESIDE THE ROW: OfDesc F T · (atDesc F T).Fits · the shared rounds open no tree below t₁ · Glues (of which g₂ alone is spent).
Limits. N IS A LETTER: that the field's r.protocol.maxBatchSize is the row's N at the frame is not shown here. THE ROW ITSELF IS NOT CLOSED: its forms are forms with letters. That the chosen Pl (PL in other files) meets the two equations is by its text:
NOT HELD HERE. NO SOUNDNESS IS CLAIMED.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DescBByMake
import Johnson.Desc.Sound.SharedJointCountRowH

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
open VerifiableInference.Desc.Shared

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD) {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (N : ℕ) (F : FileDescription (Kc.conf.X × Kc.conf.Rec)) (all : List LeftT) {X₁ X₂ W : Type}
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

/-- **FROM THE ROW's LAST CLAUSE TO THE FIELD's TYPE, TO THE LETTER.** -/
theorem field_of_laws (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (e₂ : EachLawsBN (keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂) Pl.on₂ Pl.Q₂ N 0
      ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (opens : ∀ r ∈ (DP.at a).ds₂, ∀ j ∈ r.opens, (DP.at a).t₁ ≤ j)
    (G : Glues (atDesc F T) Pl M L₁ L₂) :
    (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂ 0
        ((atDesc F T).in₂ c.1, c.2))
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁
      (fun c e => (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂ e ∧
        ((plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ e →
          (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ c))
      N (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₂ := by
  obtain ⟨g1, g2, hb⟩ := liftedAtDesc (ckP .two) (DP.at a) all _ X₁ X₂ W F T hO
  exact file_leadsBN₂ tFp tJp t3p (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁ h₂ h₃ d
    (keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂) hf
    (eachLeadsBNOfLaws _ _ _ _ _ _ _ _ _ N _ 0 e₂
      (keysByMake _ F.S₂ F.Cl W (ckP .two) _ Prod.snd
        (fun (t : (F.XiPub × F.S₁) × F.S₂) (s : F.S₂) => (t.1, s)) (DP.at a).t₁ (atDesc F T).p₂
        (atDesc F T).l₂ ((atDesc F T).in₂ d.1, d.2) g1 g2 hf.tiled₂ hb
        (fun q hq r hr => opens r
          (hf.data₂ ▸ mem_rowData (atDesc F T).p₂ (atDesc F T).l₂ q hq r hr)))) G

/-- **From the row's fifth form.** -/
theorem field_of_rowE (Ns : NumbersS) (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) W)
    (Pm : PromMeaning F.S₂) (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool)
    (ext : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at a) all).Str → W → W)
    (same : Comp → W → W → Prop)
    (row : SharedJointCountRowE (ckP .two) (DP.at a) all Kc.conf.X Kc.conf.Rec X₁ X₂ W F T Ns Mg Pm Oc
      split N ext same)
    (hon : Pl.on₂ = onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂)
    (hQ : Pl.Q₂ = stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext)
    (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (opens : ∀ r ∈ (DP.at a).ds₂, ∀ j ∈ r.opens, (DP.at a).t₁ ≤ j)
    (G : Glues (atDesc F T) Pl M L₁ L₂) :
    (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂ 0
        ((atDesc F T).in₂ c.1, c.2))
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁
      (fun c e => (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂ e ∧
        ((plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ e →
          (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ c))
      N (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₂ :=
  field_of_laws Kc DP tFp tJp t3p N F all T Pl h₁ h₂ h₃ M L₁ L₂ d hO hf
    (by rw [hon, hQ]; exact row.2.2.2) opens G

/-- THAT IT IS THE FIELD's TYPE, HELD BY LEAN: with the other two chains' premises it IS "proved verifier"'s Leads3B at these letters: the anonymous constructor takes it as the second field. -/
theorem leads3B_of_three (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (e₂ : EachLawsBN (keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂) Pl.on₂ Pl.Q₂ N 0
      ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (opens : ∀ r ∈ (DP.at a).ds₂, ∀ j ∈ r.opens, (DP.at a).t₁ ≤ j)
    (G : Glues (atDesc F T) Pl M L₁ L₂)
    (l₁ : (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).K₁.Leads
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₀
      (fun x b => (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁ b ∧
        ((plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ b →
          (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).M x b))
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₁)
    (l₃ : (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).K₃.Leads
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂
      (fun c _ => (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ c)
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₃) :
    (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).Leads3B N
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc F T).p₂ (atDesc F T).l₂ 0
        ((atDesc F T).in₂ c.1, c.2)) :=
  ⟨l₁, field_of_laws Kc DP tFp tJp t3p N F all T Pl h₁ h₂ h₃ M L₁ L₂ d hO hf e₂ opens G, l₃⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.leads3B_of_three
#print axioms VerifiableInference.OnPublicFiles.field_of_laws
#print axioms VerifiableInference.OnPublicFiles.field_of_rowE
