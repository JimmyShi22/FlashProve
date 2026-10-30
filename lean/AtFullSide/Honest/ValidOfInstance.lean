-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/ValidOfInstance.lean: the instance's key is the committer's at its own index and
coins: the premise hv of the hash build's five_of_validAt, the validity that FiveFields reads.

  valid_of_instance   the statement, from instance_is_committers.
-/
import AtFullSide.Honest.InstanceIsCommitters
import Johnson.Bind.ForProver.FiveAt

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open AtPublicFiles.Committed
open VerifierAndGoals (PublicFiles InScope)
open OnBytes.Slice (frS)
open AtPublicFiles.Key (cellsReader)
open LPFD.Full (XF instanceAsPlainRecord)
open Bind.Column (shFull)
open Bind.ForProver (shapeAtFull_inScope)
open P5J

/-- **The key of such an instance is the committer's at its own index and coins**: the validity that
FiveFields reads. -/
theorem valid_of_instance (Z : PublicFiles) (scope : InScope Z = true) {o : ProofFile.SecondHashFunctionArgument}
    {Zp : ProofFile.Pub} (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness)
    (s : (protocolAtFiles Z).OutOfDomainSeed) (x' : XF) :
    Bind.ForProver.validAt (Bind.ForProver.shapeOf Zp) Zp
      ⟨⟨cellsReader M⟩, ProofFile.Honest.randOf (S := frS) (cut := 402653181) ρ,
        (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf M ρ s)).pub.key⟩ := by
  obtain ⟨sd, x₀, e⟩ := instance_is_committers Z scope h M ρ s x'
  have hS : Bind.ForProver.shapeOf Zp = shFull := (shapeAtFull_inScope scope h).1
  rw [hS]
  exact ⟨sd, congrArg (fun ξ : ProofFile.Inst => ξ.pub.key) e⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.valid_of_instance
