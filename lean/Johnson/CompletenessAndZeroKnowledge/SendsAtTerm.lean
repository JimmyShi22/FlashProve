-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/SendsAtTerm.lean: the honest provers send their run values.

1.  WHAT IS CLAIMED: at an offline prover offlineProverWithEncodedTable and an online family onlineProversOfCommitter, which make up the arm of honestProvers (E2E/TheHonestProver.lean) where
    the public files make a description: SendsItsRunValues at formatStarts, for any link prover: the library's laws runValsAt_obj and
    runVals_tied. At the arm's value: sendsItsRunValues_term.
2.  honestProvers_arm: at such files the term is that arm. Where they make none it is another arm, of which this file says nothing.
3.  pr_coin_runValues_le: a coin's two run values are uniform 32-byte strings, so one of them is a given string with chance at most 2 · 2^-256.
4.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import E2E.TheHonestProver
import Johnson.CompletenessAndZeroKnowledge.RunValuesAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open Iop Hiop
open OnBytes (TableKey)
open OnBytes.Prover (ThreeProvers)
open OnBytes.Slice (frS GF)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (ProverCoinCounts Local)
open ProofFile.Honest.Term (OnlineReturn onlineMaker familyOf)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData committerCoinCountLessOne)
open P5J

/-- Given by hand, as in E2E/TheHonestProver.lean: instance search runs out of its budget here. -/
local instance (priority := high) sendsAtTermInstance1 : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) sendsAtTermInstance2 : Inhabited RunValue := ⟨fun _ => 0⟩

variable (files : PublicFiles) (parts : Parts files) (description : OfflineDescription)
  (returned : OnlineReturn files) (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)

/-- The arm of honestProvers at a description and a return of the maker. -/
abbrev honestProversGivenDescriptions : ThreeProvers (protocolAtFiles files) :=
  proversOf
    (offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
      (parts.prover description) runValueBytes runValueBytes (offlineStart description))
    (linkProver files) (onlineProverAt returned places firstChain)

/-- **At files that make a description and a return, honestProvers is the arm.** -/
theorem honestProvers_arm (hOff : offlineDescription files = .ok description)
    (hMaker : onlineMaker files = .ok returned) (hPlaces : H2U.placesOfMade returned.Z.made = .ok places)
    (hChain : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain) :
    honestProvers files parts = honestProversGivenDescriptions files parts description returned places firstChain := by
  unfold honestProvers offlineProver onlineProver
  rw [hOff, hMaker]
  simp only [hPlaces, hChain]

/-- What a coin of the arm fixes, and where the plain parts hold it. -/
def armStarts (rounds : FormatRounds) (linkRuns : FormatRuns) :
    SaltStarts (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain)) :=
  formatStarts _ rounds (rvKey parts.book runValueBytes runValueBytes)
    (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2)) linkRuns
    (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀) (pvZ files (dataAtFiles flashProveData files).P)

/-- **The arm sends its run values.** -/
theorem sendsItsRunValues_term (rounds : FormatRounds) (linkRuns : FormatRuns) (inRange : FullSizeMatrix → Prop) :
    SendsItsRunValues (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain))
      (armStarts files parts description returned places firstChain rounds linkRuns) inRange where
  offline := fun i r e κ ρ hi hρ =>
    runValsAt_obj files _ parts.book (dataAtFiles flashProveData files).P (parts.prover description) runValueBytes runValueBytes
      (offlineStart description) _ inRange i r e κ ρ hi hρ
  online := fun i r e n x κ ρ _ _ =>
    runVals_tied files returned.Z places firstChain silInst runValueBytes runValueBytes returned.B (dataAtFiles flashProveData files).P
      returned.H
      (offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
        (parts.prover description) runValueBytes runValueBytes (offlineStart description))
      (linkProver files) i r e n x κ ρ

/-- **The arm under refuseUnserved sends its run values**: the value that the statements read. -/
theorem sendsItsRunValues_term_refuse (rounds : FormatRounds) (linkRuns : FormatRuns) (inRange : FullSizeMatrix → Prop)
    (Served : FullSizeMatrix → LPFD.Full.XF → Prop) :
    SendsItsRunValues
      ((HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain)).refuseUnserved Served)
      (formatStarts ((HonestProvers.ofThreeProvers (honestProversGivenDescriptions files parts description returned places firstChain)).refuseUnserved
          Served) rounds (rvKey parts.book runValueBytes runValueBytes)
        (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2)) linkRuns
        (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀) (pvZ files (dataAtFiles flashProveData files).P)) inRange :=
  SendsItsRunValues.refuse (sendsItsRunValues_term files parts description returned places firstChain rounds linkRuns
    inRange) Served

/-! ## The chance of a given run value -/

/-- Two run values with one byte string are one. -/
theorem runValueBytes_injective : Function.Injective runValueBytes := by
  intro a b h
  funext i
  have h1 : (Array.ofFn fun j => (a j).val.toUInt8) = Array.ofFn fun j => (b j).val.toUInt8 :=
    congrArg ByteArray.data h
  have h2 : (a i).val.toUInt8 = (b i).val.toUInt8 := by
    have h3 := congrArg (fun arr : Array UInt8 => arr[i.val]?) h1
    simpa using h3
  have h4 := congrArg UInt8.toNat h2
  simp only [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (a i).isLt, Nat.mod_eq_of_lt (b i).isLt] at h4
  exact Fin.ext h4

/-- At abstract types, so that nothing unfolds. -/
theorem pr_value_le {R V : Type} [Fintype R] [Nonempty R] (f : R → V) (hf : Function.Injective f) (z : V) :
    Prob.pr (Prob.unif R) {r | f r = z} ≤ (Fintype.card R : ENNReal)⁻¹ := by
  have h1 : Prob.cnt (fun r => f r = z) ≤ 1 := Prob.cnt_le_one fun a b ha hb => hf (ha.trans hb.symm)
  rw [Prob.pr_unif_eq (fun r => f r = z), ENNReal.div_eq_inv_mul]
  calc (Fintype.card R : ENNReal)⁻¹ * (Prob.cnt fun r => f r = z : ℕ) ≤ (Fintype.card R : ENNReal)⁻¹ * 1 := by
        gcongr
        exact_mod_cast h1
    _ = _ := mul_one _

theorem card_runValue : (Fintype.card RunValue : ENNReal) = (2 : ENNReal) ^ 256 := by
  have e : Fintype.card RunValue = 2 ^ 256 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    norm_num
  rw [e, Nat.cast_pow, Nat.cast_ofNat]

/-- **A run value is a given string of bytes with chance at most 2^-256.** -/
theorem pr_runValue_le (z : ByteArray) :
    Prob.pr (Prob.unif RunValue) {v | runValueBytes v = z} ≤ ((2 : ENNReal) ^ 256)⁻¹ := by
  rw [← card_runValue]
  exact pr_value_le _ runValueBytes_injective z

/-- **runValuesSeldomZero at the honest provers' coins**: one of the two run values of a coin is a given string with chance at most 2 · 2^-256. -/
theorem pr_coin_runValues_le {A₂ A₃ : Type} [Fintype A₂] [Nonempty A₂] [Fintype A₃] [Nonempty A₃] (z : ByteArray) :
    Prob.pr (Prob.unif ((A₂ × RunValue) × (A₃ × RunValue)))
        {κ | runValueBytes κ.1.2 = z ∨ runValueBytes κ.2.2 = z} ≤ ((2 : ENNReal) ^ 256)⁻¹ + ((2 : ENNReal) ^ 256)⁻¹ :=
  le_trans (pr_runValues_le (fun v => runValueBytes v = z) fun v => runValueBytes v = z)
    (add_le_add (pr_runValue_le z) (pr_runValue_le z))

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.sendsItsRunValues_term_refuse
#print axioms VerifiableInference.Compilation.pr_runValue_le
#print axioms VerifiableInference.Compilation.pr_coin_runValues_le
#print axioms VerifiableInference.Compilation.honestProvers_arm
#print axioms VerifiableInference.Compilation.sendsItsRunValues_term
