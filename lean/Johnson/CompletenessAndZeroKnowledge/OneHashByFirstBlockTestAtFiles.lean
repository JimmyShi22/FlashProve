-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestAtFiles.lean: AT THE GOALS' DESCRIPTION, AT FILES WHERE protocolDataWellFormed SAYS YES: the honest
side of slotSystemF, at the search limits 2 ^ (work + 6) and at most 81 copies, stays within 2 ^ 48 hash
queries on every path, for any strategies and coins whose paths have their trees' depths. An upper bound
at the written data. Nothing here is a goal. It is about slotSystemF, which compile is (compile_eq_slotSystemF).
-/
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestBudget
import Johnson.Goal.Conditions.BindsAtThe
import Johnson.Goal.Conditions.KeyDepthAtThe
import Johnson.Goal.Numbers.DepthAtThe
import Johnson.Goal.Description.KeyWritten
import Johnson.Goal.Description.ProofWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Prover OnBytes.WholeKey OnBytes.FrontRoad
open VerifiableInference.AtEveryRequest (WithinBudget)

attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

/-- **WITHIN 2 ^ 48.** -/
theorem slotSystemF_two_pow_48 (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (h : (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z).D → HonestSide 256 (flashProveDescription.input Z allZeroDigest []).protocol
      (flashProveDescription.input Z allZeroDigest []).LeafBody (flashProveDescription.input Z allZeroDigest []).offlineRoundSplits (flashProveDescription.input Z allZeroDigest []).linkRoundSplits)
    (M : ℕ) (hM : ∀ d, (h d).M = M) (h81 : M + 1 ≤ 81)
    (hT : ∀ d, (h d).capT = capT (dataAtFiles flashProveData Z)) (hL : ∀ d, (h d).capL = capL)
    (hB : ∀ d, (h d).capB = capB (dataAtFiles flashProveData Z))
    (hp : ∀ d, PathsFit (flashProveDescription.input Z allZeroDigest []).queryLayout (h d))
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (flashProveDescription.input Z allZeroDigest []).Index)
    (x₀ : (flashProveDescription.input Z allZeroDigest []).Instance) (Form : Type) (parse : Parser flashProveDescription Z Form)
    (encF : TypedProof (flashProveDescription.F Z) (flashProveDescription.P Z) → Form) (bound : ℕ) :
    WithinBudget (slotSystemF flashProveDescription Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) h
        (fun _ => moreP (firstBlockTestAtDescriptionData (dataAtFiles flashProveData Z) allZeroDigest [])) s idx x₀ Form parse encF bound)
      (2 ^ 48) := by
  have eK := key_built_written Z scope live
  have eP := proof_built_written Z scope live
  have dT : (flashProveDescription.input Z allZeroDigest []).queryLayout.depthReqT = 0 := depthReqT_the Z live allZeroDigest []
  have dL : (flashProveDescription.input Z allZeroDigest []).queryLayout.depthReqL = 0 := rfl
  have dB : (flashProveDescription.input Z allZeroDigest []).queryLayout.depthReq = 6 := depth_the Z scope live
  obtain ⟨a, b, c, hs, h1, h2, h3⟩ := slotSystemF_withinBudget flashProveDescription Z allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) h s idx x₀ Form parse encF bound (q₀ := 8)
    (NC := (M + 2) * 8589982768 + 5223661230411 + (M + 1) * 1649307525166) (NP := 177887278538)
    (familyLaws_the Z).eight (fun d => firstIs_built flashProveData allZeroDigest [] Z d)
    (fun d => passFits_built flashProveData allZeroDigest [] Z d) hp
    (fun d => le_of_eq (by
      rw [← hM d]
      exact commitC_written (dataAtFiles flashProveData Z) allZeroDigest [] eK eP (h d) (hT d) (hL d) dT dL))
    (fun d => le_of_eq (proveC_written (dataAtFiles flashProveData Z) allZeroDigest [] eK eP (h d) (hB d) dB))
  exact ⟨a, b, c, hs.trans ((copies_within_two_pow_48 M).2 h81), h1, h2, h3⟩

end FlashProve

#print axioms FlashProve.slotSystemF_two_pow_48
