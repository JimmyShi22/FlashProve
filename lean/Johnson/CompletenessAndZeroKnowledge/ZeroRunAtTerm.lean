-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ZeroRunAtTerm.lean: UndoUpTo at flashProveAtFiles, from the parser's premise, at the arm of the honest provers.

1.  WHAT IS CLAIMED: where the parser undoes the writer outside ZeroRun (UndoOnBut), the parser undoes the writer up to a bound on ZeroRun.
    At the arm that bound is 6 · 2^-256: two first salts and four further run values.
2.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.ZeroRunAtBytes
import Johnson.CompletenessAndZeroKnowledge.SendsAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open Iop Hiop
open OnBytes (TableKey)
open OnBytes.Prover (ThreeProvers)
open OnBytes.FrontRoad OnBytes.WholeKey
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (ProverCoinCounts Local Purse)
open ProofFile.Honest.Term (OnlineReturn onlineMaker familyOf)
open VerifierAndGoals FlashProve FlashProve
open P5J
open Prob
open Johnson.Face
open IntegerTransformer (Settings)

/-- **UndoUpTo from UndoOnBut**: the definition itself is handed to the bridge. -/
theorem undoUpTo_of_face (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers) (limits : SearchLimits)
    (slotSalts : RequestLeafSaltLayout) {Form : Type} (parse : VerifierAndGoals.Parser flashProveDescription files Form)
    (encF : VerifierAndGoals.TypedProof (flashProveDescription.F files) (flashProveDescription.P files) → Form) {J : Type} (idx : J → (flashProveDescription.input files allZeroDigest []).Index)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop) (γ : ℝ≥0∞)
    (hU : UndoOnBut flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (flashSide files settings fallbackInstance provers starts limits slotSalts) idx Tr parse encF
      (ZeroRun (dataAtFiles flashProveData files) allZeroDigest []))
    (hγ : ∀ i x, Tr i x → ZKCP.Pr (badExp (OnBytes.FrontRoad.readOne (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (flashSide files settings fallbackInstance provers starts limits slotSalts)) i x ())
        (fun _ => {o | ZeroRun (dataAtFiles flashProveData files) allZeroDigest [] o.1.1.2 o.2}) ≤ γ) :
    UndoUpTo flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (flashSide files settings fallbackInstance provers starts limits slotSalts) idx Tr parse encF γ :=
  undoUpTo_of_undoOnBut _ _ _ _ _ _ _ _ _ _ _ γ hU hγ

/-- Given by hand, as in E2E/TheHonestProver.lean. -/
local instance (priority := high) zeroRunAtRunValueNonempty : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) zeroRunAtPurseNonempty (l : List (ProofFile.Honest.Addr × ProofFile.Honest.Due)) : Nonempty (Purse l) := ⟨Purse.any l⟩

/-- A coin's run values are refused with chance at most 2 · 2^-256. -/
theorem pr_coin_refused_le {A₂ A₃ : Type} [Fintype A₂] [Nonempty A₂] [Fintype A₃] [Nonempty A₃] :
    pr (unif ((A₂ × RunValue) × (A₃ × RunValue)))
        {κ | RefusedRuns (runValueBytes κ.1.2, runValueBytes κ.2.2)} ≤
      ((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  refine le_trans (MeasureTheory.measure_mono fun κ hκ => ?_) (pr_coin_runValues_le Fmt.zero32)
  by_contra hn
  refine hκ ⟨decide_eq_true fun e => hn (Or.inl e), decide_eq_true fun e => hn (Or.inr e)⟩

variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X) (parts : Parts files)
  (description : OfflineDescription) (returned : OnlineReturn files) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (rounds : FormatRounds) (linkRuns : FormatRuns) (limits : SearchLimits)
  (slotSalts : RequestLeafSaltLayout)

/-- **ZeroRun at the arm**: γ = 6 · 2^-256, written out. -/
theorem zeroRun_mass_arm (i : (flashProveDescription.input files allZeroDigest []).Index) (x : (flashProveDescription.input files allZeroDigest []).Instance) :
    ZKCP.Pr (badExp (OnBytes.FrontRoad.readOne (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
        (flashSide files settings fallbackInstance
          (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain))
          (armStarts files parts description returned places firstChain rounds linkRuns) limits slotSalts)) i x ())
        (fun _ => {o | ZeroRun (dataAtFiles flashProveData files) allZeroDigest [] o.1.1.2 o.2}) ≤
      (((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹)) +
        (((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹)) :=
  zeroRun_mass files settings fallbackInstance _ rounds _ _ linkRuns limits slotSalts
    (sendsItsRunValues_term files parts description returned places firstChain rounds linkRuns fun _ => True)
    pr_coin_refused_le pr_coin_refused_le i x

/-- **ZeroRun at the arm under refuseUnserved**: the value that the statements read. -/
theorem zeroRun_mass_arm_refuse (Served : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (i : (flashProveDescription.input files allZeroDigest []).Index) (x : (flashProveDescription.input files allZeroDigest []).Instance) :
    ZKCP.Pr (badExp (OnBytes.FrontRoad.readOne (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
        (flashSide files settings fallbackInstance
          ((HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain)).refuseUnserved Served)
          (pvStarts files ((HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain)).refuseUnserved
            Served) rounds (rvKey parts.book runValueBytes runValueBytes)
            (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2)) linkRuns) limits slotSalts)) i x ())
        (fun _ => {o | ZeroRun (dataAtFiles flashProveData files) allZeroDigest [] o.1.1.2 o.2}) ≤
      (((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹)) +
        (((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹)) :=
  zeroRun_mass files settings fallbackInstance _ rounds _ _ linkRuns limits slotSalts
    (SendsItsRunValues.refuse
      (sendsItsRunValues_term files parts description returned places firstChain rounds linkRuns fun _ => True) Served)
    pr_coin_refused_le pr_coin_refused_le i x

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroRun_mass_arm_refuse
#print axioms VerifiableInference.Compilation.pr_coin_refused_le
#print axioms VerifiableInference.Compilation.zeroRun_mass_arm
#print axioms VerifiableInference.Compilation.undoUpTo_of_face
