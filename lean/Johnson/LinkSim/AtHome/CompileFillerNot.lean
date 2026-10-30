-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileFillerNot.lean: at the numbers of CompileFiller.lean's example, the
premises of index privacy, taken whole, are false at homeR b Z.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome).
  not_premW_fillerNums   for all b and Z, PremW is false at the numbers fillerNums b Z, whatever
      the OOD phase's compilation data, the encoding of the OOD answers, the structure of
      parameters, the simulators, the sets of indices, seeds and true instances, and the numbers N.
  premW_salt_eq   at homeR b Z, all numbers c at which PremW holds have
      c.pre₀.length + c.ℓ = 256 + 8 * saltG, where saltG is the salt's length in bytes that the
      protocol description fixes: a table's salt's public prefix and its random bits make up p.sMT
      bits (PremW's part coins.len₀), and at homeR b Z compilerParameters.sMT is that number (sMT_R₀,
      Johnson/Goal/Conditions/MoreAtDigits.lean).
  premW_salt_bits   so 256 ≤ c.pre₀.length + c.ℓ. At fillerNums both are empty, which gives
      not_premW_fillerNums.

How it fits. link_all_met (Johnson/LinkSim/AtHome/CompileFiller.lean) gives a structure of
parameters at which the eighteen clauses on the link hold. A reader could take it for a sign that
all premises of index privacy (PremW, Johnson/WholeKey/Premises.lean) can be met there. They cannot,
and this file proves it. A negative result on link_all_met's example; no file under Johnson/LinkSim/
calls it.

Limits. One clause is used. That PremW can be met at homeR b Z at other numbers is not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileFiller
import Johnson.Goal.Conditions.MoreAtDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **Where PremW holds at homeR b Z, a table's salt's public prefix and random bits make up exactly
the length of the tree's salts**: 256 bits plus eight times the salt's length in bytes that the
protocol description fixes. -/
theorem premW_salt_eq {Sd : OutOfDomainSampleQueryLayout 256 (homeR b Z).queryLayout.K (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits
      (homeR b Z).linkRoundSplits} {cA : (homeR b Z).protocol.OutOfDomainAnswer → List (Dig 256)}
    {a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits}
    {Sm : Sims (homeR b Z).protocol} {ok : (homeR b Z).Index → Prop} {Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop}
    {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop} {c : CoinNums (homeR b Z).LeafBody} {N : NumsW}
    (hP : PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters a Sm ok Gs Ryes c N) :
    c.pre₀.length + c.ℓ = 256 + 8 * LPFD.Full.saltG (dataAtFiles flashProveData Z).G :=
  hP.coins.len₀.trans (sMT_R₀ Z)

/-- So they make up 256 bits or more. -/
theorem premW_salt_bits {Sd : OutOfDomainSampleQueryLayout 256 (homeR b Z).queryLayout.K (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits
      (homeR b Z).linkRoundSplits} {cA : (homeR b Z).protocol.OutOfDomainAnswer → List (Dig 256)}
    {a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits}
    {Sm : Sims (homeR b Z).protocol} {ok : (homeR b Z).Index → Prop} {Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop}
    {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop} {c : CoinNums (homeR b Z).LeafBody} {N : NumsW}
    (hP : PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters a Sm ok Gs Ryes c N) :
    256 ≤ c.pre₀.length + c.ℓ := by
  rw [premW_salt_eq b Z hP]
  exact Nat.le_add_right _ _

/-- **At the example's numbers PremW is false**, whatever the other parameters. -/
theorem not_premW_fillerNums (Sd : OutOfDomainSampleQueryLayout 256 (homeR b Z).queryLayout.K (homeR b Z).protocol (homeR b Z).LeafBody
      (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits) (cA : (homeR b Z).protocol.OutOfDomainAnswer → List (Dig 256))
    (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (Sm : Sims (homeR b Z).protocol) (ok : (homeR b Z).Index → Prop) (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) (N : NumsW) :
    ¬ PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters a Sm ok Gs Ryes (fillerNums b Z) N := fun hP => by
  have h : 256 ≤ 0 + 0 := premW_salt_bits b Z hP
  exact absurd h (by decide)

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.premW_salt_eq
#print axioms OnBytes.LinkSim.AtHome.premW_salt_bits
#print axioms OnBytes.LinkSim.AtHome.not_premW_fillerNums
