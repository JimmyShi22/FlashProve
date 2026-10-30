-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/FitZeta.lean: how the written error of index privacy changes under the
substitution of the explicit link prover and simulator at homeR b Z.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome). All statements hold for all b, Z and all
other parameters.
  zetaW_withLaid_add   the error zetaW (Johnson/WholeKey/Zeta.lean) at withLaidLink b Z a₀ c v₀ E
      (Johnson/LinkSim/AtHome/CompileLaid.lean) and fitNums N
      (Johnson/LinkSim/AtHome/CompileFit.lean), plus (M + 1) * N.zL and (M + 1) * N.hL, equals the
      error at a₀ and N. Here M + 1 is the number of copies, and N.zL and N.hL are N's two error
      terms for the link.
  zetaW_withLaid_le   so the error after the substitution is at most the error at a₀ and N, for
      all numbers of queries and of requests.
  zetaW_withLaid   the parameters after the substitution have a₀'s error, for any numbers.

How it fits. These are the facts of Johnson/LinkSim/SwapZeta.lean at homeR b Z, by calls, for the
substitution that Johnson/LinkSim/AtHome/CompileFit.lean uses. No other file under Johnson/LinkSim/
calls them; CompileFit.lean's head cites zetaW_withLaid_le for the error after the substitution.
They serve whoever applies index privacy after the substitution and wants the error there.

Limits. These are facts on the error's formula: they say nothing on whether the error is small, or
below 1 (the limits of Johnson/LinkSim/SwapZeta.lean apply). premW_withLaid_some (CompileFit.lean)
says only that suitable parameters exist, and does not keep their number of copies or their bounds
on attempts; so nothing about the error at such parameters follows from it. These lemmas speak of
withLaidLink by name.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileFit
import Johnson.LinkSim.SwapZeta

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
open OnBytes.LinkSim (zetaW_of_four zetaW_layNums)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Sd : OutOfDomainSampleQueryLayout 256 (homeR b Z).queryLayout.K (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  (c : CoinNums (homeR b Z).LeafBody) (v₀ : a₀.RV)
  (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL))

/-- The parameters after the substitution have a₀'s error. -/
theorem zetaW_withLaid (c' : CoinNums (homeR b Z).LeafBody) (u : NumsW) :
    zetaW (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters (withLaidLink b Z a₀ c v₀ E) c' u =
      zetaW (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters a₀ c' u :=
  zetaW_of_four (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters _ _ c' u rfl rfl rfl rfl

/-- The error after the substitution, plus (M + 1) * N.zL and (M + 1) * N.hL, equals the error at
a₀ and N. -/
theorem zetaW_withLaid_add (N : NumsW) (t n : ℕ) :
    zetaW (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters (withLaidLink b Z a₀ c v₀ E) c (fitNums N) t n +
        (((a₀.M + 1 : ℕ) : ℝ≥0∞) * N.zL + ((a₀.M + 1 : ℕ) : ℝ≥0∞) * N.hL) =
      zetaW (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters a₀ c N t n := by
  rw [zetaW_withLaid]
  exact zetaW_layNums (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters a₀ c N t n

/-- **The error after the substitution is at most the error at a₀.** -/
theorem zetaW_withLaid_le (N : NumsW) (t n : ℕ) :
    zetaW (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters (withLaidLink b Z a₀ c v₀ E) c (fitNums N) t n ≤
      zetaW (homeR b Z).queryLayout Sd (homeR b Z).compilerParameters a₀ c N t n :=
  (zetaW_withLaid_add b Z Sd a₀ c v₀ E N t n) ▸ le_self_add

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.zetaW_withLaid
#print axioms OnBytes.LinkSim.AtHome.zetaW_withLaid_add
#print axioms OnBytes.LinkSim.AtHome.zetaW_withLaid_le
