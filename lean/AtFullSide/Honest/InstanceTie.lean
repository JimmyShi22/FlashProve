-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/InstanceTie.lean: the instance of a run, in the base prover's terms. A tied
instance holds the out-of-domain sample of the object at (protocolAtFiles Z).EncodingRandomness; the base prover runs at the
plain readers of the same index and randomness. The two samples are one.

  recOf_plain    the object's sample is recAt at the plain readers.
  tiedYes_plain  so an instance of TiedYes is instanceAsPlainRecord of a request and that sample.

By what: home_is_ours' second clause (Johnson/Bind/ForProver/HomeIsOurs.lean).
-/
import AtFullSide.Honest.CommittedColumns

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open AtPublicFiles.Key (cellsReader padReader tailReader)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open OnBytes (TableKey)
open LPFD.Full (XF instanceAsPlainRecord)
open P5J

attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

local instance (priority := high) padsInstanceTie : Nonempty PadZ := pads_nonempty frS 402653181

/-- **The object's out-of-domain sample is recAt at the plain readers of the index and the coins.** -/
theorem recOf_plain (Z : PublicFiles) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).recOf M ρ e =
      Bind.ForProver.recAt frS frZ Bind.Column.shFull (entryZ M) (randZ Z ρ) e :=
  (Bind.ForProver.home_is_ours committerCoinCountLessOne Z M ρ e).2

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ X' : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ X')
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ X')

/-- **An instance of TiedYes, in the base prover's terms.** -/
theorem tiedYes_plain {Yes : FullSizeMatrix → XF → Prop} {n : ℕ} {w : WZ Z} {x : ProofFile.Inst}
    (h : TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w x) :
    ∃ x', Yes w.1 x' ∧ x = instanceAsPlainRecord (x',
                     Bind.ForProver.recAt frS frZ Bind.Column.shFull (entryZ w.1) (randZ Z w.2.1) w.2.2) := by
  obtain ⟨⟨x', hy, hx⟩, -⟩ := h
  exact ⟨x', hy, hx.trans (congrArg (fun a => instanceAsPlainRecord (x', a)) (recOf_plain Z w.1 w.2.1 w.2.2))⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.recOf_plain
#print axioms AtPublicFiles.AtFiles.tiedYes_plain
