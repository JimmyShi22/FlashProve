-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPAtHonestProversByYes.lean: E2E/CompleteAsIOPAtHonestProvers.lean with YesDebts in
place of HonDebts: the last line from the field yes, whichever rule pays it. It states no goal.

Limits. As that file: the hypotheses are shown of no value.
-/
import E2E.CompleteAsIOPAtHonestProvers
import E2E.CompleteAsIOPByYes

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (ProverCoinCounts Sides)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne)
open OnBytes.Prover (ofRecs)
open VerifiableInference.Compilation (CompleteInParts)
open P5J

local instance (priority := high) nonemptyPadZ_atHonestProversByYes : Nonempty PadZ := pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_atHonestProversByYes : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_atHonestProversByYes : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

/-- **The parts at honestProvers, from YesDebts.** -/
theorem parts_at_honestProvers_byYes (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H) {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {pT zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (d : YesDebts allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description) Relation FT
      pT zB z pF) :
    CompleteInParts (protocolAtFiles Z) (ofRecs (honestProvers Z P)) (workAtFiles Z) (copyNumberAtFiles Z)
      Relation pT 0 (zB + z + pF) := by
  have hk : offlineProver P = offlineAt P description := by simp only [offlineProver, hD]
  have hfam : famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H = onlineProverAt returned places firstChain := by
    rw [famG_eq, hG]
    rfl
  have hr : onlineProver Z =
      famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H := by
    rw [hfam]
    simp only [onlineProver, hM, hP, hC]
  have e : honestProvers Z P = proversOf (offlineAt P description) (linkProverAtFiles committerCoinCountLessOne Z)
      (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H) := by
    simp only [honestProvers, hk, hr]
  rw [e]
  exact parts_of_yesDebts committerCoinCountLessOne Z returned.Z places firstChain runValueBytes runValueBytes
    returned.B G returned.H (keyFileDescription description.source description.numbers description.later)
    P.book (P.prover description) runValueBytes runValueBytes (offlineStart description) hf d

/-- **The last line, from YesDebts.** -/
theorem theProver_of_yesDebts {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {pT zB z pF : ℝ≥0∞}
    (hsum : pT + 0 + (zB + z + pF) ≤ completenessTarget)
    (hf : (workAtFiles Z).Faithful)
    (d : YesDebts allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT pT zB z pF) :
    TheProverIsCompleteAsIOP Z P hr := fun _ _ =>
  ⟨hf, pT, 0, zB + z + pF, hsum,
    (parts_at_honestProvers_byYes P returned places firstChain description hM hP hC hD G hG hf
      d).refuseUnserved fun _ _ h => h⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.parts_at_honestProvers_byYes
#print axioms AtPublicFiles.AtFiles.HonestTerm.theProver_of_yesDebts
