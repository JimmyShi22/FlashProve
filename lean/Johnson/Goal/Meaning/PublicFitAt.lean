-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PublicFitAt.lean: AT ALL PUBLIC FILES Z: THE DATA THAT verify()'s DESCRIPTION
LAYS FOR THE KEY FILE AND THE PROOF FILE have at most two trees a round, as many items "root" as
trees, and no tree deeper than 63 (MadeFit, Johnson/Prover/Law/MadeFit.lean); so FewJ and Few0 hold
at both files' wire records; and none of the six lists has 2^20 rounds.

Why. These are premises of (T1) yes_of_prove (OnBytes/Prover/Main.lean) and of the printer's laws,
on public data alone. They hold at EVERY Z, in scope or not, live or not: the data are a
description's, made behind the makers' tests, or those of three empty lists.

Main names.
  madeFit_proofData, madeFit_keyData   at theProofData Zk, theKeyData Zk
    (Johnson/Goal/Description/ProofFold.lean, KeyFold.lean).
  madeFit_DK, madeFit_DP   AT (dataAtFiles flashProveData Z).DK | DP (Johnson/Goal/Tie/DescriptionOfData.lean), and so
    at these data laid at the frame's depth (MadeFit.at).
  fewJ_DK, few0_DK, fewJ_DP, few0_DP   FewJ | Few0 at wqWhole over them, at all other letters.
  rounds_built   the six lists' lengths are below 2^20.
  depth_lt   the frame's depth of the stored table is below 64.

It adds no strength. Calls: laidPOf_ok (Johnson/Desc/Laid/ProofFullLaw.lean); laidFixed_pinned
(Johnson/Desc/Key/SlotPassesBothTests.lean); madeFit_of_data, madeFit_empty, fewJ_wqWhole, few0_wqWhole;
theLive_frame's elder theLiveAt_frame (Johnson/Goal/Description/Live.lean); frameFitFullD_parts
(Johnson/Flat/Dec/FailsClosed.lean).

Limits. NOT SHOWN, AND NOT TO BE HAD FROM THESE TESTS: a bound on the number of ITEMS of a round;
that the two binding trees' logLeaves are below 64 (the frame's count bounds them by 2^20 alone) or
their salts at most 64 bytes; the leaf salt's length. The copy's file is not spoken of. That no list
is empty wants protocolDataWellFormed (listsFull): not called here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.MadeFit
import Johnson.Goal.Description.Lay
import Johnson.Goal.Description.Live
import Johnson.Desc.Key.SlotPassesBothTests
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Flat.Dec.FailsClosed
import Johnson.Top.Pub.CountsTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning
open OnBytes.Maker OnBytes.Slice OnBytes.Prover
open TypedOracleCompiler.Joined (FewJ Few0)
open FlashProve FlashProve
open VerifiableInference.OnPublicFiles (sizeNumbersFitAtFullSize frameFitFullD_parts cntFrameFullD)
open OnBytes.K.Arm (cntWhole)
open _root_.Run _root_.Run.PQ

/-- At the proof file's data, whatever the public files. -/
theorem madeFit_proofData (Zk : OnBytes.K.Pub) : MadeFit (theProofData Zk) := by
  cases h : proofDataAndDecisionOrRefusalAt OnBytes.secondHashFunction Zk with
  | ok p =>
    have e : theProofData Zk = p.1 := theProofDataAt_ok h
    rw [e]
    obtain ⟨F, -, -, hD, -, -⟩ := LPFD.Full.laidPOf_ok (D := p.1) (r := p.2) h
    exact madeFit_of_data hD
  | error e =>
    have e' : theProofData Zk = emptyRoundsData := by
      unfold theProofData theProofDataAt
      rw [h]
    rw [e']
    exact madeFit_empty 0

/-- At the key file's data, whatever the public files. -/
theorem madeFit_keyData (Zk : OnBytes.K.Pub) : MadeFit (theKeyData Zk) := by
  cases h : keyDataAndDecisionOrRefusalAt OnBytes.secondHashFunction Zk with
  | ok p =>
    have e : theKeyData Zk = p.1 := theKeyDataAt_ok h
    rw [e]
    unfold keyDataAndDecisionOrRefusalAt at h
    cases hX : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Zk.pol Zk.KL
        (some Zk.lay) with
    | error e => rw [hX] at h; cases h
    | ok X =>
      rw [hX] at h
      obtain ⟨m, F, -, -, -, hD⟩ :=
        VerifiableInference.Desc.Key.laidFixed_pinned (D := p.1) (r := p.2) h
      exact madeFit_of_data hD
  | error e =>
    have e' : theKeyData Zk = emptyRoundsData := by
      unfold theKeyData theKeyDataAt
      rw [h]
    rw [e']
    exact madeFit_empty 0

/-- **At the key file's data that verify()'s description lays, at all public files.** -/
theorem madeFit_DK (Z : VerifierAndGoals.PublicFiles) : MadeFit (dataAtFiles flashProveData Z).DK := by
  show MadeFit (flashProveData.keyRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z))
  unfold DescriptionData.keyRoundsOrEmpty
  split
  · exact madeFit_keyData _
  · exact madeFit_empty 0

/-- **At the proof file's.** -/
theorem madeFit_DP (Z : VerifierAndGoals.PublicFiles) : MadeFit (dataAtFiles flashProveData Z).DP := by
  show MadeFit (flashProveData.proofRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z))
  unfold DescriptionData.proofRoundsOrEmpty
  split
  · exact madeFit_proofData _
  · exact madeFit_empty 0

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → _root_.Iop.Dig 256) → C.Ch e k) (a : ℕ)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) (Z : VerifierAndGoals.PublicFiles)

theorem fewJ_DK : FewJ _ _ (wqWhole C K chal ((dataAtFiles flashProveData Z).DK.at a) tF tJ t3 silent run).sh :=
  fewJ_wqWhole C K chal _ tF tJ t3 silent run ((madeFit_DK Z).at a).few

theorem few0_DK : Few0 _ _ (wqWhole C K chal ((dataAtFiles flashProveData Z).DK.at a) tF tJ t3 silent run).sh :=
  few0_wqWhole C K chal _ tF tJ t3 silent run ((madeFit_DK Z).at a).few

theorem fewJ_DP : FewJ _ _ (wqWhole C K chal ((dataAtFiles flashProveData Z).DP.at a) tF tJ t3 silent run).sh :=
  fewJ_wqWhole C K chal _ tF tJ t3 silent run ((madeFit_DP Z).at a).few

theorem few0_DP : Few0 _ _ (wqWhole C K chal ((dataAtFiles flashProveData Z).DP.at a) tF tJ t3 silent run).sh :=
  few0_wqWhole C K chal _ tF tJ t3 silent run ((madeFit_DP Z).at a).few

end

/-- The frame's depth of the stored table is below 64. -/
theorem depth_lt : frS.P.T.a < 64 := by decide

/-- **None of the six lists has 2^20 rounds**, at all public files. -/
theorem rounds_built (Z : VerifierAndGoals.PublicFiles) :
    ((dataAtFiles flashProveData Z).DK.ds₁.length < 2 ^ 20 ∧ (dataAtFiles flashProveData Z).DK.ds₂.length < 2 ^ 20 ∧
      (dataAtFiles flashProveData Z).DK.ds₃.length < 2 ^ 20) ∧
    ((dataAtFiles flashProveData Z).DP.ds₁.length < 2 ^ 20 ∧ (dataAtFiles flashProveData Z).DP.ds₂.length < 2 ^ 20 ∧
      (dataAtFiles flashProveData Z).DP.ds₃.length < 2 ^ 20) := by
  show ((flashProveData.keyRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z)).ds₁.length < 2 ^ 20 ∧
      (flashProveData.keyRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z)).ds₂.length < 2 ^ 20 ∧
      (flashProveData.keyRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z)).ds₃.length < 2 ^ 20) ∧
    ((flashProveData.proofRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z)).ds₁.length < 2 ^ 20 ∧
      (flashProveData.proofRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z)).ds₂.length < 2 ^ 20 ∧
      (flashProveData.proofRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z)).ds₃.length < 2 ^ 20)
  unfold DescriptionData.keyRoundsOrEmpty DescriptionData.proofRoundsOrEmpty
  cases hl : flashProveData.live (VerifierAndGoals.asDescriptionFiles Z) with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide⟩
  | true =>
    simp only [if_true]
    have hf := (frameFitFullD_parts (show sizeNumbersFitAtFullSize _ _ _ _ _ _ _ _ = true from
      theLiveAt_frame OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) hl)).hcnt
    unfold cntFrameFullD cntWhole theQueries at hf
    have eK : ∀ D : WholeD, (D.at frS.P.T.a).ds₁ = D.ds₁ ∧ (D.at frS.P.T.a).ds₂ = D.ds₂ ∧
        (D.at frS.P.T.a).ds₃ = D.ds₃ := fun _ => ⟨rfl, rfl, rfl⟩
    simp only [(eK _).1, (eK _).2.1, (eK _).2.2] at hf
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      first
        | (show (theKeyDataAt OnBytes.secondHashFunction _).ds₁.length < _; omega)
        | (show (theKeyDataAt OnBytes.secondHashFunction _).ds₂.length < _; omega)
        | (show (theKeyDataAt OnBytes.secondHashFunction _).ds₃.length < _; omega)
        | (show (theProofDataAt OnBytes.secondHashFunction _).ds₁.length < _; omega)
        | (show (theProofDataAt OnBytes.secondHashFunction _).ds₂.length < _; omega)
        | (show (theProofDataAt OnBytes.secondHashFunction _).ds₃.length < _; omega)

end Meaning

#print axioms Meaning.madeFit_proofData
#print axioms Meaning.madeFit_keyData
#print axioms Meaning.madeFit_DK
#print axioms Meaning.madeFit_DP
#print axioms Meaning.fewJ_DK
#print axioms Meaning.few0_DK
#print axioms Meaning.fewJ_DP
#print axioms Meaning.few0_DP
#print axioms Meaning.depth_lt
#print axioms Meaning.rounds_built
