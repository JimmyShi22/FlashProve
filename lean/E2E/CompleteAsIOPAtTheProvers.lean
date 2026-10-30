-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPAtTheProvers.lean: the last line at the value that the final statement reads:
theProvers (Johnson/Face/HonestProversWithCompiledPart.lean), that is honestProvers
under refuseUnserved at ServedAt, at the settings that the files read.

  servedAt_of_request   ServedRequest is ServedAt: one text, read at the home bound
  TheHonestPartIsComplete   completeness as an IOP of theProvers, at ServedRequest
  theHonestPart_of_lists   it, and the form at every coin, from two lists of named statements

Limits. As E2E/CompleteAsIOPBothForms.lean. Nothing on the compiled part of honestProversAndSettingsAtFiles.
-/
import E2E.CompleteAsIOPBothForms
import Johnson.Face.HonestProversWithCompiledPart

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
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles settingsOfRead)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (CompleteAtEveryCoin ofRecs)
open VerifiableInference.Compilation (CompleteInParts CompleteIOP ServedAt theProvers)
open P5J

local instance (priority := high) nonemptyPadZ_atTheHonestPart : Nonempty PadZ :=
  pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_atTheHonestPart : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_atTheHonestPart : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

section
/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

set_option maxHeartbeats 2000000 in
/-- **ServedRequest is ServedAt**: one text, at the settings that the files read. -/
theorem servedAt_of_request {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (i : FullSizeMatrix) (x : XF)
    (h : ServedRequest committerCoinCountLessOne Z hr i x) : ServedAt Z (settingsOfRead pp) i x := by
  obtain ⟨w, prompt, output, hi, hf, hres, hb⟩ := h
  exact ⟨w, prompt, output, hi, hf, hres, hb⟩

set_option maxHeartbeats 2000000 in
/-- **And back.** -/
theorem request_of_servedAt {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (i : FullSizeMatrix) (x : XF)
    (h : ServedAt Z (settingsOfRead pp) i x) : ServedRequest committerCoinCountLessOne Z hr i x := by
  obtain ⟨w, prompt, output, hi, hf, hres, hb⟩ := h
  exact ⟨w, prompt, output, hi, hf, hres, hb⟩

end

/-- **The honest part is complete as an IOP**: at public files in scope that pass the head's test,
the protocol's provers, which refuse where a request is not served, are complete as an IOP on the
served requests. A definition, no theorem. `theHonestPart_of_lists`, below, has it at any parts,
under its premises, among them two lists of named statements (`OfflineDebts`, `OnlineDebts`); at the
parts `thePartsAt` its body is a theorem from scope, the head's test and the files' reading alone
(`complete_in_scope`, AtFullSide/Honest/CompleteAtTheFiles.lean). -/
def TheHonestPartIsComplete (Z : PublicFiles) (P : Parts Z) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) : Prop :=
  InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    CompleteOnServedRequests Z hr (theProvers Z (settingsOfRead pp) P)

/-- **From two lists of named statements, it, and the same at every coin of the prover.** The lists
are hypotheses: nothing here says that they hold. -/
theorem theHonestPart_of_lists {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
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
    (on : OnlineDebts returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z pF)
    (hsum : (kB + kH + kF) + 0 + (zB + z + pF) ≤ completenessTarget) :
    TheHonestPartIsComplete Z P hr ∧
      CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) P) (workAtFiles Z)
        (ServedRequest committerCoinCountLessOne Z hr) (kB + kH + kF) 0 (zB + z + pF) := by
  have b := bareForms_of_lists P returned places firstChain description hr hM hP hC hD G hG hf off on
  exact ⟨fun _ _ => ⟨hf, kB + kH + kF, 0, zB + z + pF, hsum,
      b.1.refuseUnserved (servedAt_of_request hr)⟩,
    b.2.refuseUnserved (servedAt_of_request hr)⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.servedAt_of_request
#print axioms AtPublicFiles.AtFiles.HonestTerm.request_of_servedAt
#print axioms AtPublicFiles.AtFiles.HonestTerm.theHonestPart_of_lists
