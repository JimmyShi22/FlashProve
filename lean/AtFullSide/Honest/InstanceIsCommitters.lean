-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/InstanceIsCommitters.lean: the instance's out-of-domain record is the committer's
own at the same matrix and randomness: an instance written of any request and of the object's
sample at a seed is what the committer's builder lays at that seed.

  key_is_committers        the key of the object's sample is committerPure's, at the seed typed back.
  instance_is_committers_at   the statement, in scope, with the seed and the bytes named.
  instance_is_committers   the same under «there are».
  tiedYes_is_committers    so an instance of TiedYes is the committer's.

«The committer» here is Bind.ForProver.committerPure shFull Zp, the builder of the explicit input.
cmAlong (E2E/TiedAtFiles.lean) is the committer at the object's types, of which the columns are
CommittedColumns.lean's. That the two committers' keys are one is not typed. T1's Term.committed is
not read here.

By what: recOf_plain (home_is_ours' second clause), keyOf_recAt, oodAt_atFull, inst_eq_xiAt.
The copy's number beside the seed is read by nothing; 0 stands there.
-/
import AtFullSide.Honest.InstanceTie
import Johnson.Bind.ForProver.KeyOfRecAt
import Johnson.Bind.ForProver.SeedBack
import Johnson.Bind.ForProver.InScope

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
open Bind.Column (shFull)
open OnBytes.Slice (NZ RecP keyOf)
open Bind.ForProver (Seed committerPure seedBack cube_full keyOf_recAt oodAt_atFull inst_eq_xiAt
  shapeAtFull_inScope)
open P5J

attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

local instance (priority := high) padsInstanceIsCommitters : Nonempty PadZ := pads_nonempty frS 402653181

/-- **The key written of the object's sample is the committer's key** at the seed typed back. -/
theorem key_is_committers (Z : PublicFiles) (scope : InScope Z = true) {o : ProofFile.SecondHashFunctionArgument}
    {Zp : ProofFile.Pub} (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness)
    (s : (protocolAtFiles Z).OutOfDomainSeed) :
    keyOf (fun β : NZ => β.val) ((protocolAtFiles Z).recOf M ρ s : RecP NZ frS.P.v 29 1) =
      (committerPure shFull Zp).ood
        ⟨⟨cellsReader M⟩, ProofFile.Honest.randOf (S := frS) (cut := 402653181) ρ,
          (seedBack cube_full s, 0)⟩ := by
  have hZ := shapeAtFull_inScope scope h
  have h3 : 3 * 1 ≤ frS.P.T.l := by
    show 3 * 1 ≤ 402653184
    omega
  have e₀ : keyOf (fun β : NZ => β.val) ((protocolAtFiles Z).recOf M ρ s : RecP NZ frS.P.v 29 1) =
      keyOf (fun β : NZ => β.val)
        (Bind.ForProver.recAt frS frZ shFull (entryZ M) (randZ Z ρ) s : RecP NZ frS.P.v 29 1) :=
    congrArg (keyOf (fun β : NZ => β.val)) (recOf_plain Z M ρ s)
  exact e₀.trans ((keyOf_recAt frS 1 40 29 cube_full h3 (entryZ M) (randZ Z ρ) s).trans
    (oodAt_atFull Zp hZ (cellsReader M) (randZ Z ρ) cube_full s).symm)

/-- **The instance's record is the committer's own, with the values named**: the seed is s typed
back, the copy's number beside it 0, and the bytes are the instance's own request and reply. -/
theorem instance_is_committers_at (Z : PublicFiles) (scope : InScope Z = true) {o : ProofFile.SecondHashFunctionArgument}
    {Zp : ProofFile.Pub} (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness)
    (s : (protocolAtFiles Z).OutOfDomainSeed) (x' : XF) :
    instanceAsPlainRecord (x', (protocolAtFiles Z).recOf M ρ s) = (committerPure shFull Zp).xi
      ⟨⟨cellsReader M⟩, ProofFile.Honest.randOf (S := frS) (cut := 402653181) ρ,
        (seedBack cube_full s, 0)⟩
      ((instanceAsPlainRecord (x', (protocolAtFiles Z).recOf M ρ s)).pub.request, (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf M ρ s)).y) :=
  inst_eq_xiAt shFull Zp ⟨cellsReader M⟩ (ProofFile.Honest.randOf (S := frS) (cut := 402653181) ρ)
    (randZ Z ρ) (seedBack cube_full s) 0 _ rfl rfl (key_is_committers Z scope h M ρ s) rfl

/-- **The instance's record is the committer's own**: the same, with the values under «there are». -/
theorem instance_is_committers (Z : PublicFiles) (scope : InScope Z = true) {o : ProofFile.SecondHashFunctionArgument}
    {Zp : ProofFile.Pub} (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness)
    (s : (protocolAtFiles Z).OutOfDomainSeed) (x' : XF) :
    ∃ (sd : Seed shFull × ℕ) (x₀ : ByteArray × ByteArray),
      instanceAsPlainRecord (x', (protocolAtFiles Z).recOf M ρ s) = (committerPure shFull Zp).xi
        ⟨⟨cellsReader M⟩, ProofFile.Honest.randOf (S := frS) (cut := 402653181) ρ, sd⟩ x₀ :=
  ⟨_, _, instance_is_committers_at Z scope h M ρ s x'⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ X' : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ X')
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ X')

/-- **An instance of TiedYes is the committer's.** -/
theorem tiedYes_is_committers (scope : InScope Z = true) {o : ProofFile.SecondHashFunctionArgument}
    (hp : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) {Yes : FullSizeMatrix → XF → Prop} {n : ℕ} {w : WZ Z}
    {x : ProofFile.Inst} (h : TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w x) :
    ∃ (sd : Seed shFull × ℕ) (x₀ : ByteArray × ByteArray),
      x = (committerPure shFull Zp).xi
        ⟨⟨cellsReader w.1⟩, ProofFile.Honest.randOf (S := frS) (cut := 402653181) w.2.1, sd⟩ x₀ := by
  obtain ⟨⟨x', -, hx⟩, -⟩ := h
  obtain ⟨sd, x₀, e⟩ := instance_is_committers Z scope hp w.1 w.2.1 w.2.2 x'
  exact ⟨sd, x₀, hx.trans e⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.key_is_committers
#print axioms AtPublicFiles.AtFiles.instance_is_committers_at
#print axioms AtPublicFiles.AtFiles.instance_is_committers
#print axioms AtPublicFiles.AtFiles.tiedYes_is_committers
