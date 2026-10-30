-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPBothForms.lean: the offline and online debts give the two forms that stand above
them: the parts over coins and challenges together, which the last line reads, and the same at every
coin, which the compiler's proved step partsGiveCompilerPremise reads beside them, at the same three
errors, both at the provers under refuseUnserved. It states no goal.

  CompleteAtEveryCoin.refuseUnserved   the form at every coin carries to these provers.
  everyCoin_of_yesDebts   that form from YesDebts.
  bareForms_of_lists, bothForms_of_lists   both forms at honestProvers, and under refuseUnserved.

Limits. As E2E/CompleteAsIOPOffline.lean. The fields are statements at every coin, so this is a list
that suffices, not what the last line alone needs.
-/
import E2E.CompleteAsIOPOffline

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.Prover
open Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.Compilation (HonestProvers)

variable {Index Instance : Type} {L : HolographicProtocol Index Instance}

/-- **The form at every coin carries to the provers under refuseUnserved.** -/
theorem CompleteAtEveryCoin.refuseUnserved {prover : HonestProvers L} {work : PartsWork L}
    {Relation Served : Index → Instance → Prop} {offlineError linkError onlineError : ℝ≥0∞}
    (h : CompleteAtEveryCoin L prover work Relation offlineError linkError onlineError)
    (hs : ∀ i x, Relation i x → Served i x) :
    CompleteAtEveryCoin L (prover.refuseUnserved Served) work Relation offlineError linkError
      onlineError where
  offline := h.offline
  link := h.link
  online := fun i x r e n hy c => by
    refine le_trans (pr_mono _ ?_) (h.online i x r e n hy c)
    intro ρ hf
    rcases hf with hw | hr
    · refine Or.inl ?_
      rcases hw with hw | hn | hh
      · exact Or.inl hw
      · exact absurd (hs i x hy) hn
      · exact Or.inr hh
    · exact Or.inr hr

end OnBytes.Prover

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open FlashProve (allZeroDigest)
open OnBytes.Prover (CompleteAtEveryCoin ofRecs everyCoin_of_honFit)
open P5J

local instance (priority := high) nonemptyPadZ_bothForms : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) nonemptyOfInhabited_bothForms {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)

/-- **The form at every coin, from YesDebts.** -/
theorem everyCoin_of_yesDebts {Yes : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {pT zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (d : YesDebts allZeroDigest [] Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT Yes FT pT zB z pF) :
    CompleteAtEveryCoin (protocolAtFiles Z)
      (ofRecs (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
        (famG Z Zp Np cF run₂ run₃ B G H)))
      (workAtFiles Z) Yes pT 0 (zB + z + pF) :=
  everyCoin_of_honFit hf
    (honFit_of_yesDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT d)

end AtPublicFiles.AtFiles

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (ProverCoinCounts Sides)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne)
open OnBytes.Prover (CompleteAtEveryCoin ofRecs)
open VerifiableInference.Compilation (CompleteInParts)
open P5J

local instance (priority := high) nonemptyPadZ_bothForms : Nonempty PadZ := pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_bothForms : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_bothForms : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

/-- **Both forms, at honestProvers as they stand, from the offline and online debts.** -/
theorem bareForms_of_lists {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {Tied TiedM}
    {kB kH kF zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (off : OfflineDebts Z (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF)
    (on : OnlineDebts returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z pF) :
    CompleteInParts (protocolAtFiles Z) (ofRecs (honestProvers Z P)) (workAtFiles Z) (copyNumberAtFiles Z)
        (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0 (zB + z + pF) ∧
      CompleteAtEveryCoin (protocolAtFiles Z) (ofRecs (honestProvers Z P)) (workAtFiles Z)
        (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0 (zB + z + pF) := by
  have d : YesDebts allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT (kB + kH + kF) zB z pF :=
    ⟨on.scope, on.live, on.laid, on.below, off.keyZero, off.keyAccepts, off.keyMeasure, on.yes,
      on.bad, on.hid, on.falls⟩
  have hk : offlineProver P = offlineAt P description := by simp only [offlineProver, hD]
  have hfam : famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H = onlineProverAt returned places firstChain := by
    rw [famG_eq, hG]
    rfl
  have hon : onlineProver Z =
      famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H := by
    rw [hfam]
    simp only [onlineProver, hM, hP, hC]
  have e : honestProvers Z P = proversOf (offlineAt P description) (linkProverAtFiles committerCoinCountLessOne Z)
      (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H) := by
    simp only [honestProvers, hk, hon]
  refine ⟨parts_at_honestProvers_byYes P returned places firstChain description hM hP hC hD G hG hf
    d, ?_⟩
  have ev := everyCoin_of_yesDebts committerCoinCountLessOne Z returned.Z places firstChain runValueBytes
    runValueBytes returned.B G returned.H
    (keyFileDescription description.source description.numbers description.later) P.book
    (P.prover description) runValueBytes runValueBytes (offlineStart description) hf d
  rw [← e] at ev
  exact ev

/-- **Both forms, at the provers under refuseUnserved, from the offline and online debts.** -/
theorem bothForms_of_lists {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {Tied TiedM}
    {kB kH kF zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (off : OfflineDebts Z (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF)
    (on : OnlineDebts returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z pF) :
    CompleteInParts (protocolAtFiles Z)
        ((ofRecs (honestProvers Z P)).refuseUnserved (ServedRequest committerCoinCountLessOne Z hr))
        (workAtFiles Z) (copyNumberAtFiles Z) (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0
        (zB + z + pF) ∧
      CompleteAtEveryCoin (protocolAtFiles Z)
        ((ofRecs (honestProvers Z P)).refuseUnserved (ServedRequest committerCoinCountLessOne Z hr))
        (workAtFiles Z) (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0 (zB + z + pF) :=
  have b := bareForms_of_lists P returned places firstChain description hr hM hP hC hD G hG hf off on
  ⟨b.1.refuseUnserved fun _ _ h => h, b.2.refuseUnserved fun _ _ h => h⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms OnBytes.Prover.CompleteAtEveryCoin.refuseUnserved
#print axioms AtPublicFiles.AtFiles.HonestTerm.bothForms_of_lists
