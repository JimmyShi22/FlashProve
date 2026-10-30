-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/PlugAtTerm.lean: the plug at the honest provers (E2E/TheHonestProver.lean).

1.  termLetters: the provers are honestProvers at each set of files, with the format's starts and slots. Their coin type hangs on a match over
    what the files make, so the starts are written at the arm, and carried to the term along the equation honestProvers_arm: saltStartsAtHonestProvers, one
    transport. Each law of the arm is carried by termStarts_elim.
2.  term_runValues: the run values at the plug.
3.  In the term's no-arm case the starts are plain; that is reached at files not in use alone, and no statement leans on it.
4.  What is claimed is an implication: this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.ThePlug
import AtFullSide.CompletenessAndZeroKnowledge.ArmInUse
import Johnson.CompletenessAndZeroKnowledge.ZeroRunAtTerm
import Johnson.CompletenessAndZeroKnowledge.SecondNumber
import Johnson.CompletenessAndZeroKnowledge.FirstNumber
import Johnson.Face.ByteSettings
import Johnson.CompletenessAndZeroKnowledge.TheProversEq
import Johnson.CompletenessAndZeroKnowledge.ParserGeneric

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest.Term (OnlineReturn)
open VerifiableInference.Desc (Chain)
open P5J
open Johnson.Face
open IntegerTransformer (Settings)

theorem pvKey_eq_readRunsT (files : PublicFiles) :
    pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀ = readRunsT (flashS files) := rfl

theorem pvZ_eq_readRunsB (files : PublicFiles) :
    pvZ files (dataAtFiles flashProveData files).P = readRunsB (flashS files) := rfl

theorem runValueBytes_size (v : RunValue) : (runValueBytes v).size = 32 := by
  simp [runValueBytes, ByteArray.size]

section Term
variable (files : PublicFiles) (parts : Parts files)

/-- Carry starts along an equation of provers. -/
def saltStartsAlongEquation {H H' : ThreeProvers (protocolAtFiles files)} (e : H = H') (s : SaltStarts (HonestProvers.ofThreeProvers H')) :
    SaltStarts (HonestProvers.ofThreeProvers H) := e ▸ s

theorem startsAlong_elim (Φ : (H : ThreeProvers (protocolAtFiles files)) → SaltStarts (HonestProvers.ofThreeProvers H) → Prop)
    {H H' : ThreeProvers (protocolAtFiles files)} (e : H = H') (s : SaltStarts (HonestProvers.ofThreeProvers H')) (h : Φ H' s) :
    Φ H (saltStartsAlongEquation files e s) := by
  subst e
  exact h

/-- The format's starts at an arm, at the byte settings' rounds and link value. -/
abbrev formatSaltStartsGivenDescriptions (description : OfflineDescription) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) :
    SaltStarts (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain)) :=
  armStarts files parts description returned places firstChain (flashRounds files) (linkRun, linkRun)

open Classical in
/-- **The format's starts at the term honestProvers**: the arm's, carried along honestProvers_arm; where the term is no arm, plain starts. -/
def saltStartsAtHonestProvers : SaltStarts (HonestProvers.ofThreeProvers (honestProvers files parts)) :=
  if h : ∃ (description : OfflineDescription) (returned : OnlineReturn files) (places : H2U.Places4)
      (firstChain : Chain TS ProofFile.Cl),
      honestProvers files parts = honestProversGivenDescriptions files parts description returned places firstChain then
    saltStartsAlongEquation files h.choose_spec.choose_spec.choose_spec.choose_spec (formatSaltStartsGivenDescriptions files parts _ _ _ _)
  else zeroSaltStarts _

/-- **A law of every arm is a law of the term, at files in use.** -/
theorem termStarts_elim (Φ : (H : ThreeProvers (protocolAtFiles files)) → SaltStarts (HonestProvers.ofThreeProvers H) → Prop)
    (hArm : ∀ description returned places firstChain,
      honestProvers files parts = honestProversGivenDescriptions files parts description returned places firstChain →
      Φ (honestProversGivenDescriptions files parts description returned places firstChain)
        (formatSaltStartsGivenDescriptions files parts description returned places firstChain))
    (hex : ∃ (description : OfflineDescription) (returned : OnlineReturn files) (places : H2U.Places4)
      (firstChain : Chain TS ProofFile.Cl),
      honestProvers files parts = honestProversGivenDescriptions files parts description returned places firstChain) :
    Φ (honestProvers files parts) (saltStartsAtHonestProvers files parts) := by
  unfold saltStartsAtHonestProvers
  rw [dif_pos hex]
  exact startsAlong_elim files Φ _ _ (hArm _ _ _ _ hex.choose_spec.choose_spec.choose_spec.choose_spec)

/-- The starts' lengths, with or without an arm. -/
theorem termStarts_lengths : (saltStartsAtHonestProvers files parts).LengthsFit 256 256 := by
  by_cases hex : ∃ (description : OfflineDescription) (returned : OnlineReturn files) (places : H2U.Places4)
      (firstChain : Chain TS ProofFile.Cl),
      honestProvers files parts = honestProversGivenDescriptions files parts description returned places firstChain
  · exact termStarts_elim files parts (fun _ s => s.LengthsFit 256 256)
      (fun _ _ _ _ _ => formatStarts_lengthsFit (fun κ => ⟨runValueBytes_size _, runValueBytes_size _⟩)
        (fun κ => ⟨runValueBytes_size _, runValueBytes_size _⟩) ⟨linkRun_size, linkRun_size⟩) hex
  · unfold saltStartsAtHonestProvers
    rw [dif_neg hex]
    exact plainStarts_lengthsFit _ 256

end Term

/-- **THE LETTERS AT THE HONEST PROVERS.** -/
def termLetters (parts : (files : PublicFiles) → Parts files) : PlugLetters :=
  ⟨fun files => HonestProvers.ofThreeProvers (honestProvers files (parts files)),
    fun files => saltStartsAtHonestProvers files (parts files), fun files => flashProveRequestLeafSaltLayout files 40⟩

theorem termLetters_fits (parts : (files : PublicFiles) → Parts files) : (termLetters parts).Fits :=
  ⟨fun files => termStarts_lengths files (parts files),
    fun files settings x₀ reading => formatSlotSalts_fit (flashLayout files settings x₀ reading) 40⟩

/-! ## What the arm gives of PlugLeft -/

/-- The six run values' price: two first salts and four further values, 2^-256 each. -/
abbrev sixTimes : ℝ≥0∞ :=
  (((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹)) +
    (((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹))

section Left
variable (parts : (files : PublicFiles) → Parts files) (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)

/-- **The run values at the plug.** -/
theorem term_runValues (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (reading : FlashReading files) :
    RunValuesAreSent (flashLayout files (settingsOfRead pp) neverBuiltRequest reading)
      (proversAtFiles files hr ((termLetters parts).provers files))
      ((plugPartAt (termLetters parts) files (settingsOfRead pp) hr).compiledSettings reading) rangeAtFiles :=
  termStarts_elim files (parts files)
    (fun H s => RunValuesAreSent (flashLayout files (settingsOfRead pp) neverBuiltRequest reading)
      (proversAtFiles files hr (HonestProvers.ofThreeProvers H))
      (theSettings files (settingsOfRead pp) neverBuiltRequest (proversAtFiles files hr (HonestProvers.ofThreeProvers H))
        (s.underRefusal (ServedRequest committerCoinCountLessOne files hr)) (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) reading)
      rangeAtFiles)
    (fun d r p c _ => runValuesAreSent_formatStarts _ _ _ _ _ _ _ _ _
      (SendsItsRunValues.refuse (sendsItsRunValues_term files (parts files) d r p c _ _ rangeAtFiles) _))
    (honestProvers_arm_in_use files (parts files) scope live)

end Left

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.term_runValues
#print axioms VerifiableInference.Compilation.pvKey_eq_readRunsT
#print axioms VerifiableInference.Compilation.pvZ_eq_readRunsB
#print axioms VerifiableInference.Compilation.termStarts_elim
#print axioms VerifiableInference.Compilation.termLetters_fits
