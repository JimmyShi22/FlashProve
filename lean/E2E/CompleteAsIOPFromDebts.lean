-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPFromDebts.lean: completeness as an IOP at the three provers proversOf (offlineProverWithEncodedTable …)
(linkProverAtFiles …) (famG …), from the named statements of HonDebts at no seed set aside, and the work bits'
laws. It states no goal.

Limits. HonDebts is a hypothesis: no value of its letters is shown to meet it. This is at offlineProverWithEncodedTable and
famG, not yet at honestProvers (E2E/TheHonestProver.lean). Relation is a letter; below asks that it
lies in RyesZ. At the form at every coin.
-/
import Johnson.Prover.All.CompleteAsIOPOfHonFit
import E2E.CompleteAsIOPAtFiles
import E2E.RoadHonDebts

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open FlashProve (allZeroDigest)
open OnBytes.Prover (CompleteAtEveryCoin ofRecs parts_of_honFit everyCoin_of_honFit)
open VerifiableInference.Compilation (CompleteInParts)
open P5J

local instance (priority := high) nonemptyPadZ_fromDebts : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) nonemptyOfInhabited_fromDebts {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

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

/-- **The form at every coin, from the named statements.** -/
theorem everyCoin_of_debts {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {pT zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (d : HonDebts allZeroDigest [] Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT Relation FT
      (fun _ _ => ∅) 0 pT zB z pF) :
    CompleteAtEveryCoin (protocolAtFiles Z)
      (ofRecs (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
        (famG Z Zp Np cF run₂ run₃ B G H)))
      (workAtFiles Z) Relation pT 0 (zB + z + pF) :=
  everyCoin_of_honFit hf
    (honFit_of_honDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT d)

/-- **The parts, from the named statements.** -/
theorem parts_of_debts {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {pT zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (d : HonDebts allZeroDigest [] Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT Relation FT
      (fun _ _ => ∅) 0 pT zB z pF) :
    CompleteInParts (protocolAtFiles Z)
      (ofRecs (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
        (famG Z Zp Np cF run₂ run₃ B G H)))
      (workAtFiles Z) (copyNumberAtFiles Z) Relation pT 0 (zB + z + pF) := by
  have p : CompleteInParts (protocolAtFiles Z)
      (ofRecs (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z)
        (famG Z Zp Np cF run₂ run₃ B G H)))
      (workAtFiles Z) (lettersZ Z allZeroDigest []).letters.Sd.num Relation pT 0 (zB + z + pF) :=
    parts_of_honFit (S := (lettersZ Z allZeroDigest []).letters.Sd) hf
      (honFit_of_honDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT d)
  have e : (lettersZ Z allZeroDigest []).letters.Sd.num = copyNumberAtFiles Z :=
    funext fun k => funext fun π => num_letters Z allZeroDigest [] k π
  rw [e] at p
  exact p

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.everyCoin_of_debts
#print axioms AtPublicFiles.AtFiles.parts_of_debts
