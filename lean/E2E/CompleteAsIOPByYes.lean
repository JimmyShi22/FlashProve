-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPByYes.lean: the same road as E2E/CompleteAsIOPFromDebts.lean, with one field in
place of six. HonFit, and so the parts, do not read ThreadsC: honFit_link takes YesAt, that the
description's decision accepts the three views of the honest run, at every input that is tied and
every list of challenges outside the abort set and the fall. So what is under YesAt is free:
yesAt_of_debts by ThreadsC, or a rule that asks the yes at the run alone. It states no goal.

  YesZ   YesAt at the public files Z.
  honFit_of_yes   honFit_atFiles with hyes in place of start, PlainAt, ServesAt and ThreadsAt.
  YesDebts   HonDebts with the field yes in place of start, halved, rooted, ready₁, serves, threads.
  parts_of_yesDebts   the parts from YesDebts at no seed set aside.

Limits. As E2E/RoadHonDebts.lean: the fields are hypotheses.
-/
import E2E.CompleteAsIOPFromDebts
import E2E.RoadRowsPaid

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull silP front₀ join₀ relationsAndEncodingOfClaims)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed allZeroDigest)
open OnBytes.Prover (HonFit ThreeProvers Falls CompleteAtEveryCoin ofRecs parts_of_honFit)
open VerifiableInference.Compilation (CompleteInParts)
open P5J

local instance (priority := high) nonemptyPadZ_byYes : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) nonemptyOfInhabited_byYes {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- YesAt at the public files Z: that the description's decision accepts the honest run's three
views, at inputs of TiedX, at every coin and every passing list of challenges outside the abort set
and the fall. -/
abbrev YesZ (TiedX : ℕ → WZ Z → ProofFile.Inst → Prop) : Prop :=
  YesAt (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty (descZ Zp Np cF) silInst B G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
    (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z) (kOf (lettersZ Z c₀ m₀))
    (_root_.Run.chalP .two _) TiedX

variable {Yes : FullSizeMatrix → XF → Prop}

/-- **HonFit from the verdict at the run.** -/
theorem honFit_of_yes (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (S : SdOf (lettersZ Z c₀ m₀)) (hS : NumReads Z c₀ m₀ S) (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hT) (hL) (FT) (FL) (Zs) {ζ pT pL zB z pF : ℝ≥0∞}
    (g : NineFit hT hL (lettersZ Z c₀ m₀).W FT FL Zs S Yes ζ pT pL)
    (hyes : YesZ c₀ m₀ Z Zp Np cF run₂ run₃ B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs))
    (hb : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z)
    (hf : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) (fun n w a
      => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a)) pF) :
    HonFit (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) (fallsOf hT hL _ FT FL (guardFall Zs
      (fallG Z Zp Np cF run₂ run₃ B G H)))
      (lettersZ Z c₀ m₀).W S Yes Zs ζ pT pL (zB + z + pF) :=
  honFit_link (lettersZ Z c₀ m₀) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
    ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF)
      (extZ Z) S hT hL
    FT FL Zs g (full_atFiles Z scope live) (carries_atFiles Z) (run_atFiles Z Zp Np cF live L)
    (fun n r2 r3 w a h => sil_atFiles Z Zp Np cF run₂ run₃ B G H n r2 r3 w a h.2.2)
    hyes
    (extIsEnc_famG Z Zp Np cF run₂ run₃ B G H)
      (validOut Z Zp Np cF run₂ run₃ B G H hY (AtPublicFiles.AtZero.itemsZero_of_data L.data) Zs) hb hz
      (validYes Z Zp Np cF run₂ run₃ B G H hY (AtPublicFiles.AtZero.itemsZero_of_data L.data)) hf
    (num_link (lettersZ Z c₀ m₀) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF)
        (extZ Z) S hS
      (fun _ _ _ _ _ _ _ => rfl))

variable (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)

/-- **What is left to show, with the verdict at the run as one field.** -/
structure YesDebts (Yes : FullSizeMatrix → XF → Prop)
    (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT))
    (pT zB z pF : ℝ≥0∞) : Prop where
  scope : InScope Z = true
  live : protocolDataWellFormed (asDescriptionFiles Z) = true
  laid : ∃ (D : WholeD) (r : LPFD.Full.RunPF),
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF
  below : ∀ i x, Yes i x → RyesZ Z i x
  keyZero : KeyZeroAt (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT
  keyAccepts : KeyAccepts (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT
    (fun _ _ => ∅) Yes
  keyMeasure : KeyMeasure (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) FT Yes pT
  yes : YesZ c₀ m₀ Z Zp Np cF run₂ run₃ B G H
    (TiedOut Z Zp Np cF run₂ run₃ B G H Yes fun _ _ => ∅)
  bad : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB
  hid : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
    (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (instanceAsPlainRecord a)) z
  falls : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H)
    (fun n w a => TiedOut Z Zp Np cF run₂ run₃ B G H Yes (fun _ _ => ∅) n w (instanceAsPlainRecord a)) pF

/-- **HonFit from YesDebts.** -/
theorem honFit_of_yesDebts {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)}
    {pT zB z pF : ℝ≥0∞}
    (d : YesDebts c₀ m₀ Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT Yes FT pT zB z pF) :
    HonFit (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H))
      (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _ FT (fun _ _ _ => ∅)
        (guardFall (fun _ _ => ∅) (fallG Z Zp Np cF run₂ run₃ B G H)))
      (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd Yes (fun _ _ => ∅) 0 pT 0 (zB + z + pF) := by
  obtain ⟨D, r, L⟩ := d.laid
  exact honFit_of_yes c₀ m₀ Z Zp Np cF run₂ run₃ B G H d.scope d.live L
    (lettersZ Z c₀ m₀).letters.Sd (num_letters Z c₀ m₀) d.below
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) FT (fun _ _ _ => ∅) (fun _ _ => ∅)
    (nineFit_link c₀ m₀ b Z d.scope d.live (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)
      (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) FT (fun _ _ => ∅)
      (keyFive_of_four (extIsEnc_obj Z Fx BT (dataAtFiles flashProveData Z).P HT _ shT) d.keyZero d.keyAccepts
        (seedsAside_none _ _ _) d.keyMeasure))
    d.yes d.bad d.hid d.falls

/-- **The parts, from YesDebts.** -/
theorem parts_of_yesDebts {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)}
    {pT zB z pF : ℝ≥0∞} (hf : (workAtFiles Z).Faithful)
    (d : YesDebts allZeroDigest [] Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT Yes FT pT zB z pF) :
    CompleteInParts (protocolAtFiles Z)
      (ofRecs (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
        (famG Z Zp Np cF run₂ run₃ B G H)))
      (workAtFiles Z) (copyNumberAtFiles Z) Yes pT 0 (zB + z + pF) := by
  have p : CompleteInParts (protocolAtFiles Z)
      (ofRecs (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
        (famG Z Zp Np cF run₂ run₃ B G H)))
      (workAtFiles Z) (lettersZ Z allZeroDigest []).letters.Sd.num Yes pT 0 (zB + z + pF) :=
    parts_of_honFit (S := (lettersZ Z allZeroDigest []).letters.Sd) hf
      (honFit_of_yesDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT d)
  have e : (lettersZ Z allZeroDigest []).letters.Sd.num = copyNumberAtFiles Z :=
    funext fun k => funext fun π => num_letters Z allZeroDigest [] k π
  rw [e] at p
  exact p

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.honFit_of_yes
#print axioms AtPublicFiles.AtFiles.parts_of_yesDebts
